# A boundary-defect extension principle for simple Kobon arrangements

Working manuscript prepared for Alejandro Zarzuelo Urdiales · 20 September 2026

**Status.** This draft contains a geometric proof and a Lean-checked finite counting core. The connection from Euclidean arrangements to that core is proved below in ordinary mathematics; it has not been formalized end to end in Lean. Priority for the quantitative formulation has not been established. The statement is more restricted than the universal full-gain recurrence proposed in the March paper.

## Abstract

We give an explicit one-line extension bound for simple arrangements of either an odd or an even number of real affine lines. If an arrangement of $n\ge3$ lines has $T$ bounded triangular cells and $d=n(n-2)-3T$ unused bounded segments, an exterior line can be added while preserving every existing triangle and creating at least

\[
\left\lceil\frac{n-1}{2n}\max\{3,n-d\}\right\rceil
\]

new triangles. The proof relates unused segments to unbounded two-sided cells and averages their visibility over the $2n$ possible direction sectors. In particular, an arrangement of $2m+1$ lines with at most two unused bounded segments admits an extension with exactly $m$ additional triangles. Thus the odd-to-even extension proposed by Zarzuelo holds for every simple odd arrangement attaining the usual segment-count upper bound. A finite boundary criterion treats both parities, and the general bound can be iterated without assuming that the full gain persists. We distinguish these statements from the stronger unrestricted recurrence, which remains unproved here.

## 1. Scope and notation

An arrangement is **simple** if its lines are distinct, no two are parallel, and no three are concurrent. A triangle means a bounded triangular cell of the arrangement. Let $t(A)$ count those cells and let

\[
K_s(n)=\max\{t(A): A\text{ is a simple arrangement of }n\text{ lines}\}.
\]

The subscript distinguishes this maximum from the classical Kobon number $K(n)$, which permits multiple intersections. Every construction here also gives a lower bound for classical $K$, since $K(n)\ge K_s(n)$. A numerical lower bound for classical $K(n)$ coming from a nonsimple arrangement cannot automatically be used as an input to the defect formula below.

Each line of a simple $n$-line arrangement has $n-2$ bounded elementary segments and two unbounded rays. A bounded segment belongs to at most one triangular cell: its endpoints determine its supporting line and the two other supporting lines, whose intersection can lie on only one side of the segment. Consequently

\[
d(A):=n(n-2)-3t(A)\ge0
\tag{1}
\]

is exactly the number of unused bounded segments.

An **unbounded wedge** is a two-sided unbounded cell with a finite vertex and two free boundary rays. Its opening is less than $\pi$. Write $b(A)$ for the number of these wedges. A free ray has no further arrangement vertex in its direction.

## 2. Boundary wedges and unused segments

**Lemma 1.** For every simple arrangement of $n\ge3$ lines,

\[
3\le b(A)\le n,\qquad b(A)+d(A)\ge n.
\tag{2}
\]

**Proof.** There are $2n$ free rays. At the endpoint of one such ray, precisely one other line crosses. The ray bounds an unbounded wedge if and only if that other line also has a free ray at the same endpoint. The two free rays then enclose a pointed sector. No other line can enter that sector: it would have to intersect one of its free boundary rays. Thus each wedge uses two free rays, and each free ray belongs to at most one wedge. This proves $b\le n$ and leaves $2n-2b$ unpaired free rays.

Consider an unpaired free ray on a line $L$, with endpoint $p=L\cap M$. The point $p$ is an interior vertex along $M$, so the two elementary segments of $M$ incident with $p$ are bounded. They cannot both belong to triangles. Any triangle using either of these segments must use the unique bounded segment of $L$ starting at $p$; two such triangles would share that segment, which is impossible. Charge the unpaired free ray to one of the unused segments of $M$ incident with $p$.

An unused segment can receive at most one charge at each endpoint. Therefore $2n-2b\le2d$, which proves $b+d\ge n$.

Finally, take the convex hull of all finite arrangement vertices. It has at least three vertices, because three of the original lines already supply three noncollinear points. At each hull vertex, both incident lines have free rays starting there, and hence determine an unbounded wedge. Distinct hull vertices give distinct wedges. Thus $b\ge3$. ∎

## 3. Exact counting of exterior extensions

Order the directions of the $2n$ free rays cyclically as $r_0,\ldots,r_{2n-1}$, with indices modulo $2n$. Since the two directions of every line are opposite,

\[
r_{i+n}=-r_i
\]

as directions. The two rays bounding a wedge are consecutive in this order. Otherwise a line with a direction strictly inside the wedge would eventually enter that wedge and cross one of its supposedly free boundary rays.

Let $B\subset\mathbb Z/(2n)$ contain $i$ exactly when the rays in directions $r_i,r_{i+1}$ bound a wedge. Then $|B|=b(A)$. Define

\[
c_j=\bigl|B\cap\{j,j+1,\ldots,j+n-2\}\bigr|,
\qquad C(A)=\max_j c_j.
\tag{3}
\]

**Lemma 2.** The largest triangle gain obtainable by a line strictly beyond all old vertices on one side is exactly $C(A)$. Every such addition preserves all old triangles, and

\[
\sum_{j=0}^{2n-1}c_j=(n-1)b(A),\qquad
C(A)\ge\left\lceil\frac{(n-1)b(A)}{2n}\right\rceil,
\qquad C(A)\le\lfloor n/2\rfloor.
\tag{4}
\]

**Proof.** Choose a nonzero linear functional $w$ that is nonzero on every old line direction. Precisely $n$ consecutive ray directions satisfy $w(r)>0$, say $r_j,\ldots,r_{j+n-1}$. Every cyclic block of $n$ directions can be obtained in this way by choosing $w$ in the corresponding open direction sector.

Choose

\[
H>\max_{p\text{ an old vertex}}w(p),\qquad L=\{x:w(x)=H\}.
\tag{5}
\]

This line is nonparallel to every old line and contains no old vertex. It misses every old bounded cell, since such a cell is the convex hull of its vertices. All old triangles are therefore preserved.

A wedge with vertex $p$ and free boundary directions $u,v$ is closed into a triangle precisely when both $w(u)$ and $w(v)$ are positive. In that case, $L$ intersects both free rays beyond $p$, and the resulting triangle lies wholly in the original wedge. Conversely, a new triangle using $L$ must have two old lines meeting at an old vertex $p$. Its two old sides extend beyond all old intersections to reach $L$; for those sides to be elementary segments in the enlarged arrangement, their old parts must have been free rays. Hence every new triangle arises from one of these wedges. The gain is exactly $c_j$.

Each wedge-start index belongs to exactly $n-1$ of the $2n$ cyclic intervals in (3). Double-counting gives the sum in (4), and its average gives the lower bound. Finally, wedges have disjoint pairs of free rays. A block of $n$ rays contains at most $\lfloor n/2\rfloor$ complete pairs. ∎

The coordinates in (5) make the construction explicit: inspect the finite list of direction sectors, choose one maximizing $c_j$, and take, for example, $H=1+\max_p w(p)$. Rational input lines admit a rational choice of $w$ in every such open sector and consequently a rational added line.

## 4. An extension theorem valid for both parities

**Theorem 3 (extension bound).** Let $A$ be a simple arrangement of $n\ge3$ lines, with $t(A)=T$ and $d=n(n-2)-3T$. There is a line $L$ such that $A\cup\{L\}$ is simple, every old triangle is preserved, and

\[
t(A\cup\{L\})\ge T+
\left\lceil\frac{n-1}{2n}\max\{3,n-d\}\right\rceil.
\tag{6}
\]

**Proof.** Lemma 1 gives $b(A)\ge\max\{3,n-d\}$. Apply Lemma 2. ∎

Equivalently, define, for integers $n\ge3$ and $T\ge0$,

\[
g(n,T)=\left\lceil
\frac{n-1}{2n}\max\{3,\,3T-n(n-3)\}
\right\rceil.
\tag{7}
\]

Then the following implication holds **for every $n\ge3$, of either parity**:

\[
\boxed{K_s(n)\ge T\quad\Longrightarrow\quad
K_s(n+1)\ge T+g(n,T).}
\tag{8}
\]

To justify using a lower bound $T$ in place of the exact count, take a witnessing arrangement with actual count $T'\ge T$. Both $g(n,T)$ and $T+g(n,T)$ are nondecreasing in $T$, so (6) for $T'$ implies (8).

**Iteration.** Starting from any certified simple $s$-line arrangement with at least $T_s$ triangles, set

\[
T_{n+1}=T_n+g(n,T_n),\qquad n\ge s\ge3.
\tag{9}
\]

Then $K_s(n)\ge T_n$ for every $n\ge s$. This is an unconditional construction scheme covering all subsequent line counts. It does not say that these lower bounds are records. The guaranteed gain may be smaller than $\lfloor n/2\rfloor$.

## 5. Recovering the full odd-to-even gain

**Corollary 4.** If $A$ has $2m+1$ lines, $m\ge1$, and at most two unused bounded segments, an exterior line can be added while preserving all old triangles and creating exactly $m$ new triangles.

**Proof.** Lemma 1 gives $b\ge2m-1$. If every sector created at most $m-1$ triangles, Lemma 2 would give

\[
2m(2m-1)\le2m b
=\sum_j c_j
\le(4m+2)(m-1)=2m(2m-1)-2,
\]

a contradiction. Hence some sector gives at least $m$; Lemma 2 permits at most $m$. ∎

For odd $n$, attaining the segment-count upper bound

\[
t(A)=\lfloor n(n-2)/3\rfloor
\]

leaves either zero or two unused segments. Thus Corollary 4 applies to **every simple odd arrangement attaining that bound**, including the $n\equiv1\pmod6$ case with two unused segments.

The precise maximum-function consequence is

\[
K_s(2m+1)=\left\lfloor\frac{(2m+1)(2m-1)}3\right\rfloor
\quad\Longrightarrow\quad
K_s(2m+2)\ge K_s(2m+1)+m.
\tag{10}
\]

This closes the geometric extension step for upper-attaining odd inputs. It does not establish that such inputs exist for every odd number of lines.

**Even-to-odd sufficient condition.** For $n=2m\ge4$, the condition $b(A)\ge2m-1$ guarantees $C(A)=m$. Indeed,

\[
(2m-1)b(A)\ge(2m-1)^2>4m(m-1),
\]

so one sector has gain at least $m$, and Lemma 2 gives the opposite inequality. This condition is sufficient, not necessary. More generally, the exact necessary and sufficient condition for a full-gain exterior extension, in either parity, is the finite test $C(A)\ge\lfloor n/2\rfloor$.

## 6. Infinite-family corollary with explicit attribution

Parpalak and Utkin supply simple straight-line arrangements attaining the odd upper bound for every $n=18\cdot2^t+1$, using the Bartholdi–Blanc–Loisel iterative construction. This is their input family. [Parpalak–Utkin, arXiv:2604.22035](https://arxiv.org/abs/2604.22035).

Taking $q=18\cdot2^t$, Corollary 4 gives

\[
\boxed{K_s(q+2)\ge\frac{q^2}{3}+\frac q2-1,
\qquad t\ge0.}
\tag{11}
\]

The proof is immediate but unconditional relative to that published input construction: the odd arrangement has $q^2/3-1$ triangles and defect two, so the additional line contributes $q/2$. The first resulting even orders and counts are $20:116$, $38:449$, $74:1763$, and $146:6983$.

This is an attributed corollary, not a claim that the seed, doubling method, or these even bounds were first discovered here. For the established $q=6\cdot2^t$ odd family, the same argument yields $K_s(q+2)\ge q^2/3+q/2-1$. The perfect odd families also fall under Corollary 4 with defect zero. [Bartholdi–Blanc–Loisel, arXiv:0706.0723](https://arxiv.org/abs/0706.0723).

## 7. What the stronger recurrence would require

The natural full-gain statement covering both parities is

\[
\mathcal E_s:\qquad K_s(n+1)\ge K_s(n)+\lfloor n/2\rfloor,
\qquad n\ge3.
\tag{12}
\]

It consists of two assertions:

\[
\begin{aligned}
K_s(2m+2)&\ge K_s(2m+1)+m &&(m\ge1),\\
K_s(2m+1)&\ge K_s(2m)+m &&(m\ge2).
\end{aligned}
\]

Equation (12) is **a conjectural strengthening in this draft**. Theorem 3 proves a weaker, unconditional rule for both parities; Corollary 4 proves the first full-gain assertion under a precise saturation hypothesis. Neither result establishes the full second assertion for all even maxima.

There are also different quantifiers to keep separate. A recurrence for maxima need not imply that one can extend every fixed arrangement while keeping its old triangles. Conversely, showing that one proposed line fails does not refute a recurrence for maxima.

For example, the five lines $y=ix+i^2$, $i=0,\ldots,4$, have three triangles. Adding $y=x/2+100$ preserves them and creates only one new triangle. This contradicts the March paper's unqualified alternating-segment lemma, but does not disprove the existence of a better added line or (12). These two counts and simplicity are checked in `RationalExamples.lean`.

Full-gain exterior steps also need not persist under iteration. The explicit seven-line example in that file has ten triangles and cyclic boundary profile

\[
(2,2,2,1,1,1,1,1,1,1,1,2,1,1).
\]

Its largest exterior gain is two, below $\lfloor7/2\rfloor=3$. The boundary algorithm verifies this finite profile exactly. Interior line additions and other arrangements are not excluded by this observation.

## 8. Formal verification and reproducible examples

`BoundaryExtension.lean` proves the cyclic sum identity, the averaging bound, the defect-based numerical consequence, the odd defect-two implication, and an even boundary criterion. It also proves that (12), as a statement about an arbitrary function, is equivalent to its two parity cases. All theorem checks terminate successfully with Lean 4.31.0 and the pinned Mathlib revision. The axiom audit contains only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or added geometric axiom.

`RationalExamples.lean` uses kernel reduction (`decide +kernel`) to verify simple rational arrangements with counts $5\to7\to10$ at orders $5\to6\to7$, covering both parity transitions, and the counterexample to the unqualified alternating-segment assertion. These are examples, not a proof by induction of (12).

The general Euclidean lemmas in Sections 2–3 still need an end-to-end Lean formalization. The checked cyclic results explicitly take their finite boundary data and numerical hypotheses as inputs. They do not silently assume the universal extension theorem.

The accompanying exact rational program checks two independent triangle-counting methods on the small examples and a $19\to20\to21$ chain with counts $107\to116\to126$. The 19-line input is credited to Parpalak–Utkin. The last step is a separately certified interior addition; the chosen 20-line arrangement has exterior capacity nine. None of these finite demonstrations is presented as a new Kobon record. An additional deterministic test set covers 560 simple arrangements at orders 3 through 30.

## 9. Positioning the contribution

The method of adding an exterior line has earlier precedents. Bartholdi–Blanc–Loisel explicitly discuss extensions of perfect odd arrangements; Blanc also obtains several even examples by adding a distant line. Blanc's unused-segment arguments are relevant antecedents for the incidence counting used here. [BBL, Introduction after Theorem 1.1](https://arxiv.org/html/0706.0723v1); [Blanc, Sections 2 and 5](https://arxiv.org/html/0801.2845v2).

The contribution claimed by this manuscript is its **explicit quantitative formulation in terms of the unused-segment defect, its exact finite boundary criterion for either parity, and its proof of the extension step for all simple odd arrangements with defect at most two**. These give a rigorous formulation of Zarzuelo's March 2026 extension proposal. They should not be described as the first use of exterior addition, a proof of the full recurrence (12), a new best lower bound for every $n$, or a complete Lean formalization of the geometry. Whether the displayed quantitative bound is new in the literature remains to be determined.

Original proposal: [Zarzuelo Urdiales, *New Lower Bounds for Even Kobon Numbers*, Archivara](https://archivara.org/paper/48b411c9-0e03-4592-931e-179b9a1c2312); [public formalization](https://github.com/alejandrozu/kobon-proof).
