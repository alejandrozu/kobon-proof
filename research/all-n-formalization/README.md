# A verified Kobon lower bound at every natural order

Prepared for Alejandro Zarzuelo Urdiales, 20 September 2026; updated 22 September 2026.

## The unconditional result

Write `K(n)` for the classical Kobon maximum. The strongest completed universal
construction now gives

\[
G(n)=\begin{cases}0&0\le n\le2,\\
1&n=3,\\
\lfloor n(n-3)/3\rfloor+1+(n\bmod2)&n\ge4.
\end{cases}
\]

`Kobon.Universal.baseline_sound` constructs an actual **simple** real-line
arrangement attaining this lower bound for every natural order. This is a
kernel-only general theorem, not a consequence inferred from finite tests.
The earlier baseline remains proved and is retained below as part of the
construction's history:

\[
B(n)=\begin{cases}0&0\le n\le2,\\
\lceil n(n-3)/3\rceil&n\ge3.
\end{cases}
\]

Let `C(n)` be the value in the [finite exception table](exceptions.md), and zero
at every unlisted order. The current delivered all-order formula is

\[
\boxed{L(n)=\max\{G(n),C(n)\},\qquad K(n)\ge L(n)\quad(n\in\mathbb N).}
\]

`Kobon.Universal.all_n` is the current unconditional geometric existence theorem.
It has no assumption asserting a full-gain extension, a published construction,
or a growing-order family. The bound dominates all **138** saved finite
certificates, including **104** simple witnesses. `AllN.all_n` retains the
earlier `max(B,C)` envelope, whose generated exception table now contains **64**
strict finite enhancements over B. Since G dominates B, `Universal.bound` is
equivalently `max(G, AllN.bound)`. It equals G for every `n > 195` in this release.

For `n>=4`, the exact gains G-B in residue classes 0 through 5 modulo 6 are
`1,1,0,2,0,1`. Thus the current theorem strictly improves the quoted classical
ceiling formula at infinitely many orders, not merely at the finite exceptions.

This is the maximum of a proved refinement of a classical construction and the
strongest saved finite witnesses. It is not a claim of being the best possible
bound derivable from those witnesses, the best known value at each order, or a
new asymptotic record. The catalogue now includes the current externally
published nonsimple witnesses at 8:15, 14:54, 20:117, 26:204, 32:315, 38:450 and
50:792, with source attribution and independent exact recounts.

The case distinction is an explicit, computable formula, not an optimization
over unknown arrangements. To construct its witness, use the indexed saved
coordinates at an exceptional order, or the trigonometric construction below
at any other order, using the phase/chart refinement described next. Values
0, 1 and 2 use elementary zero-triangle arrangements.

## The stronger phase and affine-chart construction

The shifted arrangement uses `theta_i=(i+1/6)pi/n` in the same line equation
displayed below. Its selected triples have index sum 0 or n-1 modulo n. A
sharper repeated-index overlap count proves `floor(n(n-3)/3)+1` for every
`n>=3`. For odd orders, one- and two-cap projective changes of affine chart give
the additional triangle needed by G. The actual determinant signs, exposed-cap
inequalities, retained triangles, simplicity and counts are all proved in Lean.

See [the complete phase/chart account](../six-hour-2026-09-21/phase-proof.md) and
[the primary-source priority audit](../six-hour-2026-09-21/general-bounds/lower-bound-priority-audit.md).
The underlying family belongs to Füredi and Palásti. Their projective count
table contains related constant terms, so first numerical priority for this
affine refinement is not established. The complete explicit Lean construction
and its comparison with B are established results.

## The classical part is now proved geometrically in Lean

The original all-order construction belongs to Zoltán Füredi and Ilona Palásti,
*Arrangements of lines with a large number of triangles*, Proc. AMS 92(4),
561–566 (1984), DOI [10.1090/S0002-9939-1984-0760946-2](https://doi.org/10.1090/S0002-9939-1984-0760946-2).
Its role as an all-order affine Kobon lower bound is also recorded in
[Triangle areas in line arrangements](https://real.mtak.hu/114794/7/1-s2.0-S0012365X20302910-main.pdf), Section3.1.
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
successive recurrence. The current envelope uses the saved 49:767 and 50:792
witnesses (the latter exceeds the required791), then the classical baseline
for all `n >= 51`. The comparison is explained by

\[
\frac{n(n-3)}3-
\left(\frac{(n-1)^2}4+191\right)
=\frac{(n-51)(n+45)}{12}\ge0\qquad(n\ge51).
\]

The current stronger envelope gives, for example, 51:818, 52:850 and 60:1141, whereas
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
| `AllN.dominates_every_saved_certificate` | All 138 retained finite inequalities are covered |
| `AllN.strict_improvements` | Strict improvement over B at the 64 finite exception orders |
| `AllN.polynomial_gap` | Arithmetic gap from Tamura's polynomial is at most `floor(n/3)`; this does not prove Tamura's upper-bound theorem |
| `AllN.from_49_unconditional` | The former 49-seed numerical target, now without its recurrence assumption |
| `ShiftedFurediPalasti.simple_lower_bound` | Actual simple phase-shifted construction with `floor(n(n-3)/3)+1` triangles |
| `FurediPalastiWrap.one_cap_simple_lower_bound`, `FurediPalastiTwoCaps.two_cap_simple_lower_bound` | Actual projective changes of affine chart retaining the extra bounded triangles |
| `Universal.baseline_sound` | A simple real arrangement attaining G for every natural order |
| `Universal.baseline_improvement` | Exact residue-sensitive gain over B |
| `Universal.all_n` | The current total lower bound `max(G,C)` |
| `Universal.dominates_49_target` | The current envelope also dominates the original 49-seed numerical target |

The general baseline geometry and count use only `propext`, `Classical.choice`
and `Quot.sound`. The finite enhancement reuses the existing `native_decide`
certificates and therefore also trusts Lean's native evaluation. No placeholder
or new geometric axiom is used. The finite formula comparisons use kernel
reduction. The original March files remain archived and outside the active build.

The predicate `LowerBound` uses distinct nondegenerate empty supporting triples
in real line arrangements. `Kobon.Cells` now proves that these triangles have
nonempty interiors equal to strict arrangement sign cells, and that distinct
certified triangles have disjoint interiors. This replaces the older warning
that the local-to-cell bridge was wholly absent. No topological equivalence is
silently introduced as an axiom; the exact proved cell statements are listed
in the root formalization audit.

## What is new, and what is not

The classical all-order quadratic baseline is prior work from 1984. Taking a
maximum with a finite catalogue is an elementary consolidation. The current
completed work adds the explicit phase/chart refinement G, its complete
real-coordinate Lean proof, and integration with the updated saved witnesses.
The leading term remains n²/3-n; numerical first priority for G is unestablished.

The compatible eleven-line seed and the quantitative boundary-defect analysis
remain separate research directions. The older additional-line values at
39,51,99 and195 are now numerically superseded by G itself, so their absence
from an explicit OEIS row is not evidence of a distinctive numerical result.
The following highlights compare the current envelope with B:

| n | Baseline B(n) | L(n) | Gain |
|---:|---:|---:|---:|
| 39 | 468 | 470 | 2 |
| 44 | 602 | 608 | 6 |
| 51 | 816 | 818 | 2 |
| 81 | 2106 | 2132 | 26 |
| 82 | 2160 | 2172 | 12 |
| 99 | 3168 | 3170 | 2 |
| 161 | 8480 | 8532 | 52 |
| 162 | 8586 | 8612 | 26 |
| 195 | 12480 | 12482 | 2 |

These comparisons do not establish first discovery or domination of every
earlier construction. The other exceptions include older published optima,
reproductions and the previously OEIS-attributed Zarzuelo values. None of the
64 finite exceptions is automatically a new discovery just because it is in this table.

The separate sparse hybrid-family formula would supply infinitely many strict
improvements over the baseline if its geometric iteration were connected to
the already formalized seed. That remains an additional Lean task. It is not
assumed by the present all-order theorem.

A defensible description is:

> We provide an unconditional Lean-verified lower-bound function for every
> natural order, combining a complete real-coordinate proof of a parity-sensitive
> affine refinement of the Füredi–Palásti construction with certified finite
> enhancements. Its universal baseline is `floor(n(n-3)/3)+1+(n mod2)` for n at
> least four. It dominates the classical ceiling benchmark everywhere and
> improves it at infinitely many orders. The finite inputs retain their
> individual attributions; numerical first priority for the affine refinement
> and the full geometric doubling iteration remain separate questions.

## Reproduction

The repository pins Lean 4.31.0 and Mathlib. From a checkout with the dependencies
available:

```sh
lake build Kobon.FurediPalastiCount Kobon.FurediPalasti Kobon.AllN Kobon.Universal
lake build Kobon.Audit
python scripts/generate_all_n.py
python scripts/evidence_manifest.py --check
```

The full audit is `python scripts/verify_lean.py --jobs 2`. The all-order formula
generator only selects existing theorem references; its output is independently
checked by Lean. `exceptions.json` records every value, gain, source file and
theorem name. `exceptions.md` is the complete human-readable table of finite
enhancements **over B**; some of these are already supplied by G. The generator
preserves the historical `AllN` envelope and does not replace `Universal`.
