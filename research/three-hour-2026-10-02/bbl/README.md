# Recursive BBL geometry: 2 October 2026

## Completed milestones

The previously formalized one-step BBL construction now closes a genuine
geometric seed invariant. The following new modules have compiled with the
pinned Lean 4.31.0 toolchain, and their main declarations report only
`propext`, `Classical.choice`, and `Quot.sound`:

* `Kobon/BBLRecursiveWitness.lean`, `canonical_step`: retains the actual
  canonical arrangement, its simplicity, crossing order, central triangle,
  positive central apex, all next-grid distinguished triangles, and the
  counted witness of at least `T + (4*r)^2` actual triangles.
* `Kobon/BBLRecursiveGrid.lean`, `graph_reindex`: the explicit interleaving
  permutation puts the output back into exactly the tangent-grid input form
  with parameter `2*r` and the same epsilon.
* `Kobon/BBLRecursiveSeed.lean`, `seed_step`: actual saturated geometric seeds
  are closed under doubling, for `r >= 5` and
  `0 < epsilon < tan(alpha(r)/2)`.
* `Kobon/BBLInfinite.lean`, `uniform_iterate`, `infinite_family`: a whole
  sufficiently-small-positive-epsilon seed family can be iterated to every
  finite depth. The permitted epsilon interval is allowed to shrink with
  depth; no fixed epsilon valid for infinitely many levels is asserted.
* `Kobon/BBLRecursiveChoice.lean`, `canonical_eventually`: for every good
  delta, all sufficiently small positive kappa provide the complete witness.
  This stronger selection form allows simultaneous boundary conditions.

The permutation/list transport used in this proof is supplied independently
by `Kobon/Permutation.lean` in the same session.

## Formula and its scope

Starting from a compatible seed with `q0 = 4*r` nonhorizontal lines and at
least `T0` triangles, put `q_t = q0 * 2^t`. The recursive triangle count obeys

```
T_(t+1) = T_t + q_t^2,
3*T_t + q0^2 = 3*T0 + q_t^2.
```

For the existing 21-line seed (`q0=20`, `T0=132`), this is

```
n_t = 20*2^t + 1,
T_t = (400*4^t - 4)/3 = (q_t^2 - 4)/3.
```

The concrete connection is now complete: `BBLSeed21Normalized.compatible`
and `BBLSeed21Visible.compatible` supply the sorted triangle and visible
seeds. `BBLVerifiedFamilies.odd_family` and `.even_family` prove the actual
infinite families, and `.eleven_odd_family` / `.eleven_even_family` include
the original 11-line seed as level zero. Thus, for every natural `t`, with
`q = 10*2^t`,

```
SimpleLowerBound (q+1) ((q^2-4)/3)
SimpleLowerBound (q+2) ((q^2-4)/3 + q/2).
```

The generic recursion has only Lean's three standard axioms. The concrete
odd family additionally inherits four pre-existing native certificate checks
from `BBLSeed21`: directions, distinguished checks, simplicity, and triangle
checks. The even family also inherits admissibility and visible-pair checks,
for six native certificate dependencies in total. There is no `sorryAx` and
no new mathematical axiom. Native computation remains an explicitly stated
trust boundary; these six checks are not being described as kernel-only.

These are formalization advances for a BBL construction and the existing
compatible seed. They do not establish a new numerical record or transfer
historical credit for the BBL method.

## The even invariant is now closed

`BBLRightmost.canonical_row_eventually` proves the actual central new line
is the final intersection on the rightmost old line. The trigonometric
maximum is combined with a positive old slope and the old clean rightward
ray; no desired visible-pair conclusion is assumed.

`BBLNextBoundary.next_rightmost_boundary` proves the new rightmost line has
the corresponding clean ray. The positive projection direction and
admissibility persist at sufficiently small pencil scale.

`BBLEvenStep.canonical_visible_step` combines these facts with continuity
of old visible wedges and the integer crossing rows. At most one old wedge
uses the distinguished line; the pencil supplies `2*r+1` fresh wedges.
Consequently the net resource gain is `2*r`.

`BBLEvenRecursive.visible_seed_step` transports the whole enhanced seed,
including its actual witness lists, through the interleaving permutation.
`BBLEvenInfinite.uniform_iterate` then proves iteration. Its resource count
is `V_t + 2*r = V_0 + 2*r*2^t`; a seed with `V_0=2*r` therefore retains the
full `q_t/2` exterior gain at every level.

All these generic theorems compiled with only `propext`, `Classical.choice`,
and `Quot.sound`.

## Consequences and limits

The theorem includes the following existence results:

| Odd lines | Triangles | Even lines | Triangles |
|---:|---:|---:|---:|
| 11 | 32 | 12 | 37 |
| 21 | 132 | 22 | 142 |
| 41 | 532 | 42 | 552 |
| 81 | 2,132 | 82 | 2,172 |
| 161 | 8,532 | 162 | 8,612 |
| 321 | 34,132 | 322 | 34,292 |
| 641 | 136,532 | 642 | 136,852 |

In particular, `642:136852` is now an infinite-theorem consequence even
though the second exact counter on an older particular 642-line coordinate
file had not finished. The new theorem establishes existence and does not
retroactively certify that coordinate file.

The geometric recurrence is on a compatible family, not on every optimal
arrangement and not an unrestricted one-line successor rule. It does not
repair the original March recurrence by assuming it. Nor does it establish
a new numerical record: BBL and the prior compatible seed retain their
historical attribution. The new result is the completed recursive geometric
formalization, including the formerly conditional full even gain.

The odd counts are one below the classical quadratic benchmark
`floor(n*(n-2)/3)`. The even counts are one below the stronger benchmark for
simple arrangements, `floor(n*(2*n-5)/6)`. The latter is not a general upper
bound for arbitrary arrangements with multiple intersections. The Lean
benchmark module proves these arithmetic identities. The later
`UpperSimpleOptimality`, `UpperEvenSimpleOptimality`, and `BBLFamilyOptimality`
modules additionally establish actual upper bounds and one-triangle windows
for simple arrangements in both parities.

The compatible 33- and 49-line seed branches did not complete their full Lean
checks before the release freeze. Their sources are preserved as
[unverified drafts](../drafts/README.md). Those instantiations are not part of
the completed claims above; the separate exact computational evidence remains
available for the next research session.

## Exact obstruction to one optimal-seed fitting pattern

`BBLTangentAlgebra`, `BBLTangentValues`, and `BBLGridObstruction` now prove
one explicit ten-sign obstruction directly for the real tangent grid.
The final `actual_grid_orientation_impossible` theorem holds for every real
epsilon and arbitrary reciprocal slopes, including epsilon-dependent slopes
with no boundedness assumption. Its entire proof has only the standard three
Lean axioms, without native finite checks. See `TANGENT_OBSTRUCTION.md` for
the exact signs, weights, provenance, and classification-scope limits.
