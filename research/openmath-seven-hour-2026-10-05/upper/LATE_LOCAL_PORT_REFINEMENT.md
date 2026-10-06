# Final local-port refinement, 6 October 2026

The final additional all-triple global bound is

```
2*delta + B15 >= 2*U + 3*(E3+P21) + N12 + M22.
```

`M22` counts actual cores with ordinary shared degree two, core shared
degree two, and at least one marked outgoing port. The other notation and
the pairwise nonparallel/all-core-triples scope are the same as in
`VERIFIED_PROGRESS.md`. There is no extra local resource assumption in the
final actual theorem.

The new local theorem is

```
markedCount(p) + degreeFrom(A0,p) <= coreDegree(p).
```

Outgoing marked edges have poor opposite endpoints, extracted by
`MarkedPorts.marked_edge_spec`. Incoming antipodal-source edges have an
opposite endpoint in `A0`, whose ordinary shared degree is two. Those edge
sets are therefore disjoint unless the center itself belongs to `A0`; in
that case its marked count is zero. Both sets lie in the actual incident
shared-core edge set, so finite union cardinality proves the resource
inequality.

At an `M22` core the unit-discharge weight is zero and its marked count
`m>=1`. The new inequality gives `m+x<=2`, hence `2*m-x>=1`. This retains
one extra unit in the existing unit charging proof. The finite weight
lemma displays the resource hypothesis explicitly; the actual arrangement
wrapper derives it from the local theorem. Final double-recipient
elimination remains supplied by the completed actual N13 geometry.

Sources:

* [LocalPortBudget](../../../Kobon/UpperOpenMathLocalPortBudget.lean),
  `certificate_marked_plus_anti_degree_le`.
* [M22GainWeights](../../../Kobon/UpperOpenMathM22GainWeights.lean),
  `finite_m22_curvature_gain`.
* [M22Curvature](../../../Kobon/UpperOpenMathM22Curvature.lean),
  `certificate_m22_source_free_defect_bound`.

The scratch proofs passed before 04:52 UTC with only `propext`,
`Classical.choice`, and `Quot.sound`. Active-source replay is recorded in
[local-port replay](late-local-port-builds/openmath-upper-local-port-budget-promoted.log),
[finite-weight replay](late-local-port-builds/openmath-upper-m22-gain-weights-promoted.log), and
[actual-wrapper replay](late-local-port-builds/openmath-upper-m22-curvature-promoted.log); the research branch performs
the final release replay. No closed-component M22 refinement or new
unrestricted numerical Kobon optimum is claimed by this late addition.
