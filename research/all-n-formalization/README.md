# A verified Kobon lower bound at every natural order

Prepared for Alejandro Zarzuelo Urdiales, 20 September 2026.

## The unconditional result

Write `K(n)` for the classical Kobon maximum. Define

\[
B(n)=\begin{cases}0&0\le n\le2,\\
\lceil n(n-3)/3\rceil&n\ge3.
\end{cases}
\]

Let `C(n)` be the value in the finite exception table below, and zero at every
unlisted order. Our delivered all-order formula is

\[
\boxed{L(n)=\max\{B(n),C(n)\},\qquad K(n)\ge L(n)\quad(n\in\mathbb N).}
\]

`Kobon.AllN.all_n` is an unconditional geometric existence theorem. It has no
assumption asserting a full-gain extension, a published construction, or a
growing-order family. The bound dominates all 86 saved finite certificates and
strictly improves the ceiling form of the classical benchmark at 52 orders.
It equals that benchmark for every `n > 195` in this release.

This is the maximum of a fully proved classical baseline and the strongest
saved finite witnesses. It is not a claim of being the best possible bound
derivable from those witnesses, the best known value at each order, or a new
asymptotic record. In particular, the catalogue does not yet contain several
stronger externally known nonsimple small-order witnesses.

The case distinction is an explicit, computable formula, not an optimization
over unknown arrangements. To construct its witness, use the indexed saved
coordinates at an exceptional order, or the trigonometric construction below
at any other order. Values 0, 1 and 2 use elementary zero-triangle arrangements.

## The classical part is now proved geometrically in Lean

The original all-order construction belongs to Zoltán Füredi and Ilona Palásti,
*Arrangements of lines with a large number of triangles*, Proc. AMS 92(4),
561–566 (1984), DOI [10.1090/S0002-9939-1984-0760946-2](https://doi.org/10.1090/S0002-9939-1984-0760946-2).
Its role as an all-order affine Kobon lower bound is also recorded in
[Triangle areas determined by arrangements of planar lines](https://nagyzoli.web.elte.hu/Triangles.pdf).
Tamura's familiar formula is an upper bound, not a competing lower construction.

Our Lean proof supplies actual real lines, with

\[
\theta_i=\frac{(i+1/2)\pi}{n},\qquad
\sin\theta_i\,x+\cos\theta_i\,y=\sin(3\theta_i),
\quad 0\le i<n.
\]

The determinant of two normals is `sin(theta_i - theta_j)`, so the lines are
pairwise nonparallel. A checked trigonometric factorization expresses the
evaluation of the third line at a homogeneous pair intersection as

\[
4\sin(x-y)\sin(z-y)\sin(z-x)\sin(x+y+z).
\]

The selected supporting triples satisfy `i < j < k` and

\[
i+j+k\equiv n-1\text{ or }n-2\pmod n.
\]

The sign proof establishes nondegeneracy and shows that every other line has
one weak sign at all three vertices. Thus these are empty triangles in the
repository's explicit real-coordinate definition.

For either residue there are `n^2` ordered modular solutions. At most `3n` have
a repeated index. The residues are distinct; each increasing triple accounts
for at most six ordered solutions. Consequently the number `T` of selected
triangles satisfies

\[
6T\ge2n^2-6n,\qquad T\ge\lceil n(n-3)/3\rceil.
\]

Both the general geometry and this general count are proved in Lean. The proof
does not infer a universal theorem by testing finitely many values. The ceiling
is integral rounding of the classical construction, not claimed new mathematics.

## The original 49-seed numerical target is now unconditional

There is a second useful theorem in the new file:

\[
\boxed{K(n)\ge\left\lfloor\frac{(n-1)^2}{4}\right\rfloor+191,
\qquad n\ge49.}
\]

`AllN.from_49_unconditional` proves this without assuming the proposed
successive recurrence. It uses the saved 49:767 and 50:791 witnesses, then the
classical baseline for all `n >= 51`. The comparison is explained by

\[
\frac{n(n-3)}3-
\left(\frac{(n-1)^2}4+191\right)
=\frac{(n-51)(n+45)}{12}\ge0\qquad(n\ge51).
\]

The stronger envelope gives, for example, 51:817, 52:850 and 60:1140, whereas
the former target gives 816, 841 and 1061. The target's numerical inequality
has therefore been established; the statement
`K(n+1) >= K(n) + floor(n/2)` has not. Nor does the new proof construct each
successor by preserving the immediately previous witness. It chooses a valid
construction separately for every order.

## Formal statements and trust

| File/theorem | Meaning |
|---|---|
| `Kobon/FurediPalastiCount.lean`, `ordered_bound` | Arbitrary-order modular count |
| `Kobon/FurediPalasti.lean`, `lower_bound` | Actual real-line baseline for every `n >= 3` |
| `Kobon/AllN.lean`, `baseline_sound` | Baseline for every natural `n`, including 0, 1, 2 |
| `AllN.enhancement_sound` | Every exceptional value has a saved geometric witness |
| `AllN.all_n` | `LowerBound n (bound n)` for every natural `n`, with no geometric premises |
| `AllN.dominates_every_saved_certificate` | All 86 retained finite inequalities are covered |
| `AllN.strict_improvements` | Strict improvement over the baseline at the 52 listed orders |
| `AllN.polynomial_gap` | Arithmetic gap from Tamura's polynomial is at most `floor(n/3)`; this does not prove Tamura's upper-bound theorem |
| `AllN.from_49_unconditional` | The former 49-seed numerical target, now without its recurrence assumption |

The general baseline geometry and count use only `propext`, `Classical.choice`
and `Quot.sound`. The finite enhancement reuses the existing `native_decide`
certificates and therefore also trusts Lean's native evaluation. No placeholder
or new geometric axiom is used. The finite formula comparisons use kernel
reduction. The original March files remain archived and outside the active build.

The predicate `LowerBound` uses distinct nondegenerate empty supporting triples
in real line arrangements. A separate equivalence with a topological
connected-component definition of arrangement cells remains outside the library,
as explained in the root formalization audit. No such equivalence is silently
introduced as a Lean axiom.

## What is new, and what is not

The all-order quadratic baseline is prior work from 1984. Taking a maximum with
a finite catalogue is an elementary consolidation, not a newly invented
geometric construction. The new completed work in this release is a formal
real-coordinate proof of that baseline and its integration with all saved
certificates into one total, proved formula.

The research novelty candidates remain the explicit additional-line witnesses,
the compatible eleven-line seed, and the quantitative boundary-defect analysis.
The nine finite highlights contribute the following improvements over this
particular classical benchmark:

| n | Baseline B(n) | L(n) | Gain |
|---:|---:|---:|---:|
| 39 | 468 | 469 | 1 |
| 44 | 602 | 608 | 6 |
| 51 | 816 | 817 | 1 |
| 81 | 2106 | 2132 | 26 |
| 82 | 2160 | 2172 | 12 |
| 99 | 3168 | 3169 | 1 |
| 161 | 8480 | 8532 | 52 |
| 162 | 8586 | 8612 | 26 |
| 195 | 12480 | 12481 | 1 |

These comparisons do not establish first discovery or domination of every
earlier construction. The other exceptions include older published optima,
reproductions and the previously OEIS-attributed Zarzuelo values. None of the
52 exceptions is automatically a new discovery just because it is in this table.

The separate sparse hybrid-family formula would supply infinitely many strict
improvements over the baseline if its geometric iteration were connected to
the already formalized seed. That remains an additional Lean task. It is not
assumed by the present all-order theorem.

A defensible description is:

> We provide an unconditional Lean-verified lower-bound function for every
> natural order, combining a formal real-coordinate proof of the classical
> Füredi–Palásti construction with certified finite enhancements. The function
> dominates the classical ceiling benchmark at every order and improves it at
> 52 specified orders in the current certificate catalogue. The finite inputs
> retain their individual attributions; no new asymptotic or first-discovery
> claim follows from the envelope operation itself.

## Reproduction

The repository pins Lean 4.31.0 and Mathlib. From a checkout with the dependencies
available:

```sh
lake build Kobon.FurediPalastiCount Kobon.FurediPalasti Kobon.AllN
lake build Kobon.Audit
python scripts/generate_all_n.py
python scripts/evidence_manifest.py --check
```

The full audit is `python scripts/verify_lean.py --jobs 2`. The all-order formula
generator only selects existing theorem references; its output is independently
checked by Lean. `exceptions.json` records every value, gain, source file and
theorem name. `exceptions.md` is the complete human-readable table.
