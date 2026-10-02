# A shorter clean-line parity proof

## Mathematical argument

Let an even number `n >= 4` of distinct, pairwise nonparallel real lines be
given, and let `L` be clean: all its arrangement vertices are ordinary.
There are exactly `n-1` distinct crossings on `L`.

There is one open half-plane of `L` in which every other line has a bounded
elementary segment incident to its crossing with `L`. To see this, first try
the positive half-plane. If every transverse line has an intersection there,
take its first such vertex. Otherwise choose a transverse line `R` with no
intersection there. Every intersection of `R` with another transverse line
lies in the negative half-plane: it cannot lie on `L`, because `L` is clean.
Thus every transverse line has an intersection in the negative half-plane.
The line `R` itself does as well, since `n >= 3`. Taking the first vertex on
each transverse ray gives the desired bounded segments.

Suppose that every selected segment belongs to exactly one triangle of the
chosen certified triangle family. At its ordinary endpoint on `L`, the
triangle has only the two available supporting lines. It must therefore
have a side on `L`. The triangle's other endpoint on `L` is another ordinary
crossing, and its other transverse side lies in the same selected half-plane.
It is exactly the selected elementary segment at that crossing. Consequently
the selected triangles pair the crossings of `L`. Every crossing is covered,
and two different pairs cannot share a crossing, because its selected segment
would then belong to two triangles. This gives a partition of the odd set of
`n-1` crossings into pairs, a contradiction.

Hence some selected bounded segment has triangle degree zero or two. The
capacity-two theorem already excludes larger degree. Degree zero is an
unused edge; degree two is a shared edge. Since its endpoint on `L` is
ordinary, the shared-edge classification places it in `D1`, not `D2`.
Charging each clean line to one such edge gives

```
n - h <= 2 U + D1.
```

An unused edge receives at most one charge per ordinary endpoint, hence at
most two. A `D1` edge has exactly one ordinary endpoint and receives at most
one. At an ordinary endpoint, the clean charging line is uniquely determined
as the incident line other than the edge's supporting line. This proof also
works for a finite injective subset of certified triangles: all degrees and
unused-edge counts are relative to that same subset.

## Completed formalization

`Kobon/UpperCleanHalfplane.lean` proves the common-half-plane intersection
alternative directly from real-coordinate incidence and ordinary crossings.
It proves injectivity of the transverse-line crossing map. Its
`ordinary_vertex_pairs_on_line` theorem states that an indexed triangle at
an ordinary point of `L` has exactly one other vertex on `L`.
It also counts the actual clean crossings and rules out a two-element
partition when `n` is even. All six printed theorem roots compiled with only
the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

`Kobon/UpperCleanEdges.lean` converts farther same-side intersections into
actual members of `UpperEdgeInventory.lineEdges`: it chooses the successor
or predecessor of the clean crossing in the sorted vertex inventory. Affine
line evaluation preserves the strict sign at that adjacent vertex. Its
`common_bounded_side` theorem is the desired common-side bounded-segment
statement, with no boundedness or elementarity assumption added.

`Kobon/UpperCleanPairing.lean` proves uniqueness of the actual selected
segment from a crossing into either prescribed open side. It extracts the
consecutive-index relation from inventory membership. Two different incident
segments would have the crossing between their other endpoints; positive
affine evaluation at both endpoints would then contradict zero evaluation
at the crossing. This closes the same-side uniqueness step geometrically.

Both of these modules compiled with only the same standard axioms. All
three sources are included in the final upper-branch verifier.

`Kobon/UpperCleanCover.lean` subsequently completed the actual pair-cover
extraction. `actual_base_cover` proves that degree-one selected segments force
a disjoint cover by actual two-element triangle bases; the cover is a
conclusion, not a hypothesis. `clean_line_bad_degree` extracts the common
side and selected segments and proves that some degree differs from one.
Finally, `certificate_clean_line_charge` combines geometric capacity two and
the actual shared-edge classification to obtain an unused or D1 edge at every
even-order clean line. All these roots compiled with standard axioms only.

`Kobon/UpperCleanCharging.lean` completed the aggregate extraction. A clean
line is mapped to its actual charge edge and ordinary endpoint. This map is
injective, by uniqueness of the inventory edge's support and uniqueness of
the nonradial support at an ordinary endpoint. The finite sigma-type target
has at most two points for each unused edge and exactly one for each D1 edge.
The theorem `certificate_clean_line_budget` therefore proves
`n-h <= 2U+D1` with all quantities extracted from real coordinates. It compiled
with only the standard axioms. There is no remaining charging assumption in
this theorem.

These are geometric incidence maps, not numerical budget assumptions. The
argument replaces the repository manuscript's longer induction over the
strip of faces. The underlying parity phenomenon is classical, and
mathematical priority for this shorter formulation has not been established.
The full extracted budget applies to pairwise nonparallel real arrangements
of even order at least four and to any finite injective certified triangle
family, with unused and shared counts relative to that family. No new
unrestricted numerical Kobon upper record is claimed. Global cyclic-fan
extraction still limits the separate nonsimple numerical upper consequences.

An independent read-only review by the hybrid-family research branch found
no gap in this ordinary mathematical argument and confirmed the then-remaining
Lean scope limits, which the subsequent cover and charging modules closed.
Its durable report is
[`../bbl/INDEPENDENT_SCOPE_AUDIT.md`](../bbl/INDEPENDENT_SCOPE_AUDIT.md).
