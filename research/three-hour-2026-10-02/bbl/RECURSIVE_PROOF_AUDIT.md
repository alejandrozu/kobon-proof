# Audit of the completed recursive family

Audit date: 2 October 2026. Scope: the new BBL recursive modules and their
connection to the pre-existing parametric 21-line certificate. This is a
source/signature and compiled-axiom audit, not a claim of numerical priority.

## Exported unconditional statements

`Kobon.BBLVerifiedFamilies.eleven_odd_family (t : Nat)` proves

```
SimpleLowerBound (10*2^t+1) ((100*4^t-4)/3).
```

`Kobon.BBLVerifiedFamilies.eleven_even_family (t : Nat)` proves

```
SimpleLowerBound (10*2^t+2) ((100*4^t-4)/3+5*2^t).
```

Both statements quantify only over the natural iteration index. They have
no seed, realization, visibility, geometric-counting, or recurrence hypothesis.
The tail versions `odd_family` and `even_family` start at 21 and 22 lines.
The original 11- and 12-line cases are supplied independently by the existing
`SeedFamily.simple_lower_bound` and `HybridBoundary.seed_exterior` proofs.

`SimpleLowerBound` means actual real nonparallel straight lines, no triple
concurrence, and a duplicate-free list of at least the stated number of
nondegenerate empty triangular supporting triples. The geometric cell
interpretation and disjointness belong to the existing foundational modules;
no pseudoline realization is substituted for real straight lines.

## Dependency and hypothesis audit

| Layer | Main declaration | Actual role and input scope |
|---|---|---|
| Analytic step | `BBLRecursiveChoice.canonical_eventually` | For an actual simple saturated old tangent-grid arrangement, positive central apex, `r>=5`, valid epsilon, and an analytically certified `GoodDelta`, all sufficiently small positive scales give the complete counted output. |
| Retained witness | `BBLRecursiveWitness.canonical_step` | Chooses delta and scale and returns actual lines, central triangle, next saturation, and the full triangle witness. |
| Grid normalization | `BBLRecursiveGrid.graph_reindex` | Exact coefficient identity under a bounded bijection; no deformation or numerical approximation. |
| Odd closure | `BBLRecursiveSeed.seed_step` | Produces the same concrete geometric invariant at `2*r`, with `T+(4*r)^2` triangles. |
| Rightmost maximum | `BBLRightmost.canonical_row_eventually` | Derives the final old/new intersection from the proved trigonometric maximum and old clean rightward ray. It does not assume a desired visible wedge. |
| New boundary | `BBLNextBoundary.next_rightmost_boundary` | The actual crossing order makes the new rightmost line's intersection with the distinguished line its final rightward crossing. |
| Visible assembly | `BBLEvenStep.canonical_visible_step` | Old visible wedges away from the distinguished line persist; at most one is lost, while `2*r+1` fresh wedges are proved. Net visible gain is `2*r`. |
| Even closure | `BBLEvenRecursive.visible_seed_step` | Relabels the actual triangle and visible lists and preserves positive rightmost slope, projected direction, admissibility, and boundary. |
| Iteration | `BBLInfinite.uniform_iterate`, `BBLEvenInfinite.uniform_iterate` | Finite-depth induction from a whole sufficiently-small-epsilon seed family. |
| Concrete seed | `BBLSeed21Normalized.compatible`, `BBLSeed21Visible.compatible` | The existing 21-line coefficient family supplies every input invariant, including all nineteen ordered distinguished triangles. |
| Final families | `BBLVerifiedFamilies` | Discharges all generic seed assumptions and adds the original 11/12 cases. |

The `Seed` record has exactly these geometric fields: slopes, counted
triangle list, no parallels, no concurrency, each consecutive distinguished
triangle, positive central apex, list distinctness, triangle validity, and
count. It contains no conclusion about a future arrangement.

`VisibleSeed` additionally carries an actual visible-pair list and its count,
admissibility for the fixed projection, a positive rightmost slope, a positive
projected rightward direction, and the clean rightmost ray. Every one of these
additional fields is returned by the recursive step. The fixed projection in
the concrete family is `(10,-13)`.

## The epsilon quantifiers matter

The invariant used for iteration is

```
there exists eta>0 such that for every 0<epsilon<eta
there exists a compatible actual seed.
```

Each doubling replaces eta by at most
`min eta (tan(alpha(r)/2))`. Thus the final theorem has the logical form

```
for every finite depth t, there is a positive eta_t,
and every epsilon in (0,eta_t) admits a depth-t seed.
```

Slopes, perturbation delta, and scale kappa may depend on epsilon and depth.
There is no hidden uniformity assertion for these choices. In particular,
the theorem does **not** assert that one fixed positive epsilon can be used
at all infinitely many depths. The threshold tends downward with the grid
spacing. This is sufficient for an infinite family of finite arrangements,
which is precisely what the numerical lower-bound theorems assert.

It also does not prove an unrestricted successor recurrence from every
optimal arrangement, nor an indefinitely extendible chain from an arbitrary
fixed 49-line configuration. Those are different statements and retain their
previous status.

## Count identities and comparisons

For a seed with `q0=4*r`, triangle count `T0`, and visible count `V0`, the
generic recursion proves

```
q_t = q0*2^t,
3*T_t + q0^2 = 3*T0 + q_t^2,
V_t + q0/2 = V0 + q_t/2.
```

Consequently a seed with `V0=q0/2` keeps the full exterior gain `q_t/2`.
These identities are proved arithmetically after the geometric induction;
they are not substituted for that induction.

`BBLFamilyBenchmarks` separately proves, for `q=10*2^t`,

```
oddCount  = Universal.baseline(q+1) + (q/3-2),
evenCount = Universal.baseline(q+2) + (q/2-q/3-2),
(q+1)*(q-1)/3       = oddCount+1,
(q+2)*(2*q-1)/6     = evenCount+1.
```

Division is natural-number floor division. The first improvement is strict
at every level; the second is strict after level zero. The last two identities
compare numbers with the familiar odd classical and even simple-arrangement
quadratic expressions. They do not formalize either global upper theorem.

## Trust and verification

All generic recursive, geometric, normalization, and arithmetic benchmark
theorems printed only

```
propext, Classical.choice, Quot.sound
```

The concrete odd family additionally uses these existing native certificate
axioms from `BBLSeed21`:

* `directions._native.native_decide.ax_1_1`
* `distinguished_checks._native.native_decide.ax_1_1`
* `simple._native.native_decide.ax_1_1`
* `triangle_checks._native.native_decide.ax_1_1`

The even family also uses

* `admissible_check._native.native_decide.ax_1_1`
* `visible_checks._native.native_decide.ax_1_1`

These are finite computation dependencies already present in the seed
certificate, not assumed geometric lemmas. They should nevertheless be
reported explicitly: the concrete infinite statements are not kernel-only
with respect to those checks. No theorem in the completed chain has a
`sorryAx` dependency. Axiom logs are archived alongside this audit.

## Readiness conclusion

No accidental geometric hypothesis remains in the final family signatures.
The analytic parameter quantifiers, next-grid central orientation, full
distinguished-line saturation, counted-list transport, and visible-boundary
resource have all been closed. The remaining interpretive restrictions are
the native seed trust boundary, finite-depth rather than fixed-epsilon
infinite realization, and the distinction between this compatible family and
an unrestricted successor rule. No numerical-record priority is asserted.

## Stronger comparison with the previous verified release

`BBLFamilyBenchmarks.previous_envelope` proves that the old
`Universal.bound n` equals its baseline whenever `195<n`. Consequently
`odd_previous_gain` and `even_previous_gain` are exact improvements over the
entire old verified envelope, including its saved finite exceptions.
`strict_previous_tail t` proves strict improvement in both parities at
`10*2^(t+5)+1` and `10*2^(t+5)+2`, for every natural `t`. This is a comparison
with the previous repository release, not with every construction in the
literature. These arithmetic comparison theorems have only the standard
three axioms.

## Separate obstruction proof

`BBLTangentAlgebra`, `BBLTangentValues`, and `BBLGridObstruction` give an
independent, entirely kernel-checked obstruction for one explicitly listed
ten-sign system on the actual tangent grid. It has no native-check axioms.
It is not a premise of the infinite-family proof. See
`TANGENT_OBSTRUCTION.md` for its exact geometric statement and
`LOCAL_ROBUSTNESS.md` for a separately identified computer-assisted extension
to nearby nonuniform grids.
