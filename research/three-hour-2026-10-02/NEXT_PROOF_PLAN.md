# Concrete continuation plan after the verified release

Recorded during the final read-only review on 2 October 2026. The active
375-source library remains unchanged from the successful 19:33 UTC audit.
This note contains mathematical deductions and proposed formalization tasks,
**not additional Lean-verified theorems or new numerical Kobon bounds**.

## Small local lemmas to prove first

For an `UpperFan.Sectors n 3 L` with positive consecutive determinants, write
`u_i = point(i) - center`. Antipodality gives `u_3 = -lambda*u_0` with
`lambda > 0`. Thus

\[
\det(u_0,u_1)>0,\qquad \det(u_1,u_2)>0,\qquad
\det(u_0,u_2)=\det(u_2,u_3)/\lambda>0.
\]

The first three directions are pairwise noncollinear. Their opposite partners
therefore give six distinct, noncentral radial points. Formalizing this fact
would turn the existing theorem
`core_shared_card_eq_three_of_extremal` into a statement about three distinct
neighboring points, rather than merely three indices, for triple fans.

Next define a cyclic `Sectors.shift` and prove that it preserves shared-ray
cardinalities, antipodality, and positivity. The current triple-fan
incompatibility normalizes the common ray to index zero. A reindexing lemma
would let it apply at arbitrary incident indices.

For a shared edge joining centers `v` and `w`, the required matching at
indices `z` and `y` is

\[
f(z)=w,\quad g(y)=v,\quad
g(y-1)=f(z+1),\quad g(y+1)=f(z-1).
\]

These equalities must come from the same two certified triangles incident to
the edge. Retain their certificate indices in the extracted sector data;
the present abstract local fan record does not supply this association.

## A finite graph consequence requiring no planarity

Use actual core points as vertices and actual shared elementary edges with
two core endpoints as edges. Existing endpoint classification and two-element
edge cardinality provide the ingredients of a finite simple graph with
`D2` edges. The missing interface identifies graph degrees with the extracted
`coreShared` rays.

Let `X` be the exceptional triple cores, meaning multiplicity three and
ordinary shared-ray count `d1=3`, and let `e=|X|`. Suppose the missing
identification gives degree three at every vertex of `X`, and the matching
lemma rules out edges joining two vertices of `X`. Each edge incident to `X`
has exactly one endpoint in `X`. Counting those incidences proves

\[
3e\le D_2,\qquad D_2-2e\ge e,\qquad D_2-2e\ge D_2/3.
\]

This argument needs no planarity theorem. Distinct-neighbor identification and
the shared-edge matching are essential assumptions, not consequences of an
arbitrary assignment of fan records to graph vertices.

If **every exceptional fan is triple**, the existing conditional theorem
`UpperCoreBudget.weighted_defect_with_core_edges` then yields

\[
2\delta\ge n+2S-7I+8q+e,
\qquad
6\delta\ge3n+6S-21I+24q+D_2.
\]

Here `q` is the number of core points, `I` their total line incidence, `S`
the multiplicity loss, and `delta=n(n-2)-3T`. If all core multiplicities are
three, then `I=S=3q`, so these simplify to

\[
2\delta\ge n-7q+e,
\qquad 6\delta\ge3n-21q+D_2.
\]

This replaces a potentially negative exceptional correction by a nonnegative
quantity. It is a corollary of the counted budget, **not a stronger inequality
when its exact original `D2-2e` term is already retained**. The negative
core-count term remains. No unrestricted numerical improvement follows from
this calculation alone, and no historical-priority claim is made.

## Divide the remaining geometric extraction into two interfaces

1. **Canonical ray order.** At a core of actual multiplicity `r`, choose a
   linear functional nonzero on every radial direction, orient representatives
   positively, and sort their slopes in that half-plane. Append their
   negatives. Prove that this gives genuine cyclic order, antipodality,
   positive consecutive determinants, and the correct multiplicity.
2. **Shared-ray incidence equivalence.** Choose the nearest actual vertex
   on each bounded ray, using the existing incident-edge existence and
   uniqueness lemmas. On unbounded rays, choose a noncentral auxiliary point.
   Prove that certified triangles occupy consecutive sectors, then establish
   an equivalence between shared rays at `v` and actual shared edges incident
   to `v`. This gives `sum d1 = D1`, `sum d2 = 2*D2`, the core-endpoint map,
   and the shared-edge matching needed above.

Demanding an actual vertex on every ray would introduce a false hypothesis:
some rays are unbounded. The current `CoreFamily` also does not identify
centers injectively, tie its multiplicities to actual line incidence, or
provide the required incidence equivalences. Those facts must be proved
explicitly before using the local theorems as whole-arrangement bounds.

The independent concrete-seed continuation is recorded in
[SEED49_STATUS.md](bbl/SEED49_STATUS.md). Its next task is computational proof
decomposition; the upper-bound task above is geometric interface extraction.
