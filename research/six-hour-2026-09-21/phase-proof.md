# A stronger verified universal baseline

## Strongest completed formula

The phase argument below has now been combined with two changes of affine
chart. The complete theorem `Kobon.Universal.baseline_sound` constructs a
**simple** real-line arrangement for every natural order and gives

\[
G(n)=\begin{cases}
0,&n<3,\\
1,&n=3,\\
\left\lfloor n(n-3)/3\right\rfloor+1+(n\bmod2),&n\ge4.
\end{cases}
\qquad K(n)\ge G(n).
\]

It uses only the standard logical axioms, with no `native_decide` dependency.
The finite envelope `Kobon.Universal.bound` also retains every certified value
in `Kobon.AllN.bound`; its finite certificate dependencies are reported
separately. This envelope must not be confused with an unrestricted successor
construction or a completed proof of BBL iteration.

Relative to the previously formalized classical baseline
`B(n)=ceil(n(n-3)/3)`, for n>=4 the exact gain is:

| n mod 6 | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| G(n)-B(n) | 1 | 1 | 0 | 2 | 0 | 1 |

For odd n not divisible by three, a projective transformation with its new
line at infinity immediately inside the unique rightmost vertex makes one
additional triangular region bounded while retaining every selected old
triangle. For odd multiples of three at least nine, a chart immediately
inside the two leftmost vertices retains two additional triangles. The
convex-hull exposure inequalities, the determinant signs in the new chart,
distinctness, and the modular counts are all proved in Lean. For even orders
the phase construction below supplies the stated formula.

The leading term remains n²/3-n. The improvement is an exact constant-term
refinement on four residue classes, not a new asymptotic density. The
distance to Tamura's polynomial floor(n(n-2)/3) is exactly

`floor(n/3) + 1[n mod3=2] - 1 - (n mod2)` for n>=4.

The underlying cubic family is due to Füredi and Palásti. Their original
projective table already contains related constant terms; numerical first
priority for this affine refinement is not established. See the
[primary-source audit](general-bounds/lower-bound-priority-audit.md).

## First component: the shifted phase

The following inequality has been proved geometrically in Lean during this
session, using only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`:

\[
K(n)\ge \left\lfloor\frac{n(n-3)}3\right\rfloor+1\qquad(n\ge3).
\]

The theorem is `Kobon.ShiftedFurediPalasti.lower_bound`. Its count is
`Kobon.ShiftedCount.ordered_bound_plus`. Neither theorem uses native evaluation,
a finite test as a universal premise, or an assumed construction theorem.

## Construction and count

Set

\[
\theta_i=\frac{(i+1/6)\pi}{n},\qquad
\sin\theta_i x+\cos\theta_i y=\sin(3\theta_i),\quad0\le i<n.
\]

The factorization already proved for the classical construction applies to
these lines. The selected increasing triples have

\[
i+j+k\equiv0\ \text{or}\ n-1\pmod n.
\]

The sign argument proves that every selected triple is nondegenerate and
uncut by every other line. This is the actual real-coordinate geometry, not
just a modular count.

Each of the two residue classes has `n^2` ordered solutions. Within one class,
the three sets with a repeated index have at most `n` members each. For residue
zero, `(0,0,0)` belongs to all three sets, so their union has at most `3n-2`
members. For the other residue, the union has at most `3n` members. There are
therefore at least `2n^2-6n+2` distinct-index ordered solutions. Every increasing
triple accounts for at most six of them. Integrality yields

\[
T\ge \left\lceil\frac{n(n-3)+1}{3}\right\rceil
=\left\lfloor\frac{n(n-3)}3\right\rfloor+1.
\]

## What it improves

The previously formalized baseline was `ceil(n(n-3)/3)`. The new formula
increases it by one exactly when `3` divides `n`, and agrees with it otherwise.
It therefore improves the previous universal theorem at infinitely many
orders. This statement compares two proved formulas; it is not a claim that
the new values exceed every earlier construction in the literature.

In particular it already supplies 39:469, 51:817, 99:3169 and 195:12481,
which had earlier been obtained through a different, nonsimple construction.
Those finite values are consequently not distinctive of that additional-line
construction. The new witnesses use a phase variant of the classical
Furedi--Palasti family. The original 1984 paper remains the mathematical
antecedent, and priority for this refinement is not established by its
absence from the paper's coarse headline bound.

The experimental script `experiments/2026-09-21/phase-family/phase_census.py`
also checks the exact trigonometric sign pattern at six phases for every
order from 3 to 60. These finite checks corroborate the result but are not
dependencies of the Lean theorem.
