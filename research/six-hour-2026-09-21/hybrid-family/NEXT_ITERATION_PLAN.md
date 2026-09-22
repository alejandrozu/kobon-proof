# Exact remaining plan for infinite BBL iteration

Read-only audit of the frozen release, 22 September 2026. This is a proof
plan, not a declaration that the following theorems have been proved.
The completed theorem is `BBLDoubling.doubling`; it concludes a geometric
lower bound after one step and does not retain a recursive seed object.

## 1. Keep the recursive geometric data

Define a proposed `Compatible r epsilon T` containing slopes `m`, a nodup
triangle list of length at least `T`, simplicity of
`oldArrangement r epsilon m`, every distinguished-line triangle, and a
positive central apex height. Keep epsilon admissibility outside the
definition. The desired closure statement has the following schematic type:

```lean
-- Proposed signature; not an existing verified declaration.
seed_step
  (hr : 5 <= r) (hepsilon0 : 0 < epsilon)
  (hepsilon : epsilon < tan (alpha r / 2)) :
  Compatible r epsilon T ->
  Compatible (2*r) epsilon (T + (4*r)^2)
```

Strengthen the existing construction to return its slopes and witnesses.
Do not attempt to recover a recursive invariant from `SimpleLowerBound`
alone: that existential statement has discarded the required coordinates.

## 2. Preserve the central triangle independently of the count list

When selecting kappa, intersect the existing eventual conditions with
`central_replaced_eventually`, independently of the supplied triangle list
`ts`. That list may omit the central triangle. Saturation supplies the old
central triangle at `j=2*r-1`, and `BBLNextSaturation.next_saturated`
requires the retained triangle supported by `(2*r-1,2*r,8*r)`.

The central height itself does not need a new analytic sign argument.
`arrangement_old` and `BBLGridReindex.central_left/right` identify the next
central apex with the old apex exactly.

## 3. Transport all witnesses through the sorting permutation

Use the full permutation `f(0)=8*r` and `f(j+1)=perm(r,j)`.

- Identify each selected old/new intercept with
  `oldIntercept (2*r) epsilon j`, using `next_cut` and
  `cut_beta_left/right`.
- Supply triangle transport for all six support permutations. The current
  `Reindex` helpers cover only selected cyclic orders.
- Transport the entire nodup witness list using sorted inverse images,
  preserving its length.
- Reuse `Reindex.no_parallel_pullback` and `no_concurrent_pullback` for
  simplicity, and `BBLNextSaturation.next_saturated` for saturation.

## 4. Normalize the verified 21-line seed

`BBLSeed21` uses grouped old/new labels, so it is not already
`oldArrangement 5 epsilon m`. Its sorted nonhorizontal source labels are:

```text
[11,1,12,2,13,3,14,4,15,5,6,16,7,17,8,18,9,19,10,20]
```

Prove the graph identity after this relabeling, transport the 132-triangle
list, and use `all_distinguished` for all 19 saturation triangles. The
source central lines are **5 and 6**, not 10 and 11. Their intersection
has height `5*epsilon/2 > 0`. The existing seed theorems already hold for
every `0 < epsilon <= 1/100000`; no stronger numerical certificate is
required for this bridge.

## 5. Quantify epsilon by finite depth

Use an invariant of the form

```text
exists eta > 0, for every 0 < epsilon < eta, Compatible r epsilon T.
```

At the next depth, use the positive threshold
`min(eta, tan(alpha(r)/2))`. Slopes, delta and kappa may depend on epsilon.
Do not require a single fixed positive epsilon to serve infinitely many
doublings.

The resulting target odd family is

```text
q_t = 20 * 2^t
number of lines = q_t + 1
T_t = (q_t^2 - 4)/3.
```

This is an integration target for the published BBL construction and the
verified compatible seed, not a new numerical-priority claim. The stronger
even companion needs a separate visibility and rightmost-line invariant;
it does not follow from the recursive triangle invariant above alone.
