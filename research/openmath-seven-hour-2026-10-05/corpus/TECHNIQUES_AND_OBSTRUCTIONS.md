# OpenMath corpus: scalable techniques and checked obstructions

Research owner: Alejandro Zarzuelo Urdiales. Audit started 5 October 2026.
The archive is evidence, not a mathematical authority: old judging summaries
can precede later verification receipts.

## Source revisions

- Judging archive: `alejandrozu/openmath-2026-judging`,
  `3dee18bdf290e70b2f9a6bd98b889d1b1b60b51c`.
- Raj Harshit Srirangam: `srirangam-r/kobon_triangles`,
  `eed14659a9b2f4ca12777da5d557f2b620b966f6`.
- Rohith Poola: `Rohith18p/rsi-kobon-triangles`,
  `f462d8e18aea2a458376c523c9b6c2980237071f`.
- HTPeo: `lavaskiller/openmath-2026-htpeo`,
  `76c63b8e425e551a930060a6871b84fe3b4780db`, as recorded in
  the archive's fresh compilation receipt.

## Mechanisms worth developing

Srirangam organizes arbitrary-multiplicity upper bounds around exact edge
budgets, local redrawing, line-view automata, and rational LP transfers. The
global transfer from arbitrary geometry to every automaton constraint remains
incomplete in his packet; selected finite SAT/DP certificates do not close it.
His general-position hand theorem states, for even n and no arrangement line
through two multiple points, `3T <= n(2n-5)/2+t`, where t counts triple points.
The useful ingredients are cap blocks, claims by clean lines, and claims by
axes of two-cap triple points. See
[the original proof](https://github.com/srirangam-r/kobon_triangles/blob/eed14659a9b2f4ca12777da5d557f2b620b966f6/proofs/additional/theorem_G_even_n.md).

The bad-wedge graph has the arrangement lines as vertices. Its edges are
simple endpoint crossings that are extreme on both lines and have an opposite
triangular corner. Its degree is at most two. Srirangam's same-side argument
uses the unique crossing of the two endpoint partner lines. A cycle then has
odd length by crossing parity against one member line, while any outside
line forces its length even. Thus a cycle must use all lines and n must be
odd. At even n the graph is a forest of paths, with component count `pi=n-W`.
This yields a credit identity in his restricted structural class, but a
global Hall/capacity inequality and reconciliation of ends remain open.
The complete hand argument is at
[ALL8_NOTE3 section 5](https://github.com/srirangam-r/kobon_triangles/blob/eed14659a9b2f4ca12777da5d557f2b620b966f6/proofs/all8/ALL8_NOTE3.md).
It is not yet an unconditional numerical upper bound.

Poola's construction pipeline combines exact line deletion/insertion with
fixed tangent-grid slope search and the classical Bartholdi--Blanc--Loisel
doubling. A rational point witness must be upgraded to a whole positive
epsilon interval before the existing geometric recursion can use it. The
61-line point witness has 1190 triangles; the separate uniform certificate
under investigation retains 1182, so those counts must not be interchanged.
The 19-line seed checked here is the Parpalak--Utkin seed in Poola's rational
realization, reflected and sheared. It retains 107 cells and all17
distinguished caps for `0<epsilon<=1/100`. This is an exact external interval
certificate; it is not a new numerical optimum or a completed Lean seed.

HTPeo's independently replayed 39-line/471-cell proof is a genuine one-cell
improvement over the earlier 470 witness. Its checker architecture is useful
beyond that finite count: pure `decide +kernel` checks are split by smallest
triangle index, and the row lists are assembled by list-filter lemmas. The
archive records 55 successfully replayed custom modules under Lean4.33.1,
with standard-axiom geometric endpoints and no native evaluation dependency.
This offers a practical alternative to very large monolithic computations.

## A general charging shortcut is false

Poola's paper includes the auxiliary empirical assertion
"at most $2k$ segments are shared by two triangles", with k the triple-point
count. Its numeric generalized Blanc conjecture is a separate statement.
The exact source is
[kobon39.typ, generalized Blanc paragraph](https://github.com/Rohith18p/rsi-kobon-triangles/blob/f462d8e18aea2a458376c523c9b6c2980237071f/paper/kobon39.typ).

The auxiliary assertion already fails for eight straight lines with no
parallels and no multiplicities greater than three. Put s=sqrt2 and use

```
y=0                       (s-1)x+y=1
x+y=1                     (s+1)x+y=-1
x=-1                      -(s+1)x+y=1
-x+y=-1                   (1-s)x+y=-1
```

There are exactly7 triple points,14 bounded triangle cells, and15 elementary
edges shared by two of these cells. Both an exact chirotope computation and
an independent exact quadratic-field geometry computation confirm the
counts. All vertices, supports, triangles and shared edges are in
`shared-rule8.json`; the scripts are `check_fp_shared_rule.py` and
`verify_shared_rule8.py`. These are external exact checks, pending a direct
Lean proof of this particular counterexample.

This is the phase-zero Furedi--Palasti arrangement already investigated in
the repository's September work. The new use is an obstruction to the
contestant's auxiliary charging rule, not authorship of the arrangement.
For the family with coefficients
`(sin(pi*i/n),cos(pi*i/n),sin(3*pi*i/n))`, every pair intersects and a triple
is concurrent exactly when `i+j+k=0 mod n`; fourfold concurrence is
impossible. If d=gcd(n,3), the triple count is

```
q=(n^2-3n+2d)/6.
```

That formula follows by ordered-triple inclusion--exclusion: among n^2
solutions, the three equality conditions each remove n and their overlaps
restore2d. Exact tested values at all n4..80 and n99,120,195 also satisfy

```
T=(n^2-3n+3-d)/3,
D=(n-2)(n-3)/2,
U=0,
D-2q=(n^2-9n+18-4d)/6.
```

The all-n triangle/shared-edge formulas have not yet been promoted to a Lean
theorem. They indicate the essential obstruction: shared sides can approach
three per triple point, with a surplus over2q of quadratic size. Any upper
proof that subtracts one triangle per triple point using D<=2q therefore
needs a different global compensation mechanism.

`shared-segment-counterexamples.json` also preserves a separate rectangular
three-direction grid family and a projective image with no parallels. Those
images have high-multiplicity points. They refute extensions that merely
count all core points, but they do not supply a new counterexample within
the triple-only class. The eight-line example above does.

None of these auxiliary-rule counterexamples refutes the final numeric
even-order generalized Blanc conjecture or establishes a new Kobon optimum.

## Current priorities

1. Complete uniform seed linkage and induction, retaining all geometric
   hypotheses rather than extending point counts by arithmetic alone.
2. Extract actual cyclic sectors and shared-core incidences, then use the
   existing clean-line parity/charging proof to obtain a valid global budget.
3. Preserve the forest/Hall idea as a general resource-matching problem; do
   not assume the unfinished capacity inequality from successful examples.
4. Avoid another exhaustive small-order search unless it supplies a reusable
   seed, a local geometric theorem, or a rigorously scoped obstruction.
