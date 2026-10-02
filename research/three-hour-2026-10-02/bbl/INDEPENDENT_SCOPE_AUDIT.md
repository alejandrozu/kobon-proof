# Independent scope audit of the new upper-bound pipeline

Audit: 2 October 2026, read-only source review by the hybrid-family branch.
No upper-branch source was edited and no additional compiler was launched.
The four requested central modules were inspected together with their
geometric dependencies and the new core-counting interfaces.

**Conclusion:** no mathematical mismatch or hidden incidence/extraction
assumption was found in `UpperEdgeInventory.certificate_defect_identity`.
It is an actual geometric identity for the explicitly stated class below.
It is not an unconditional improved upper bound for the Kobon maximum.

## Exact scope of the main identity

`Kobon/UpperEdgeInventory.lean:345`, `certificate_defect_identity`, assumes:

- `n >= 2`;
- `NoParallel n L` for real indexed lines;
- a finite index type and an injective map to canonical supporting triples;
- `TrianglePredicate n L` for every selected triple.

It concludes, in integer arithmetic,

`n(n-2)-3T = sum_v r_v(r_v-2) + U - D1 - D2`.

Every vertex, multiplicity, consecutive segment, used side and shared-side
class is constructed from the actual real coordinates. No supplied edge
count, capacity-two assumption, pairwise-disjointness assumption, or assumed
global incidence formula remains in this theorem's signature. Multiple
intersections are allowed; a no-three-concurrent hypothesis is absent.

The selected family may be a proper subset of the arrangement's triangular
cells. Here `U` means segments unused by that selected family, and `D1,D2`
refer to sides shared by two selected triangles. This is mathematically
consistent: deleting a triangle changes these terms along with `T`. One must
not retain the full-family values of `U,D1,D2` after changing the family.

## Geometric and counting checks

| Source | Audit finding |
|---|---|
| `UpperVertexBudget.lean:79`, `multiplicity_identity` | Vertices are the actual image of distinct line-pair intersections. The fiber is the off-diagonal square of the actual incident-line set, giving `sum r(r-1)=n(n-1)`. No multiplicity profile is assumed. |
| `UpperVertexBudget.lean:132`, `line_interval_budget` | `n>=2` and nonparallelness ensure each line has at least one intersection vertex. Thus the cast of `v_i-1` is legitimate, including the all-concurrent case. The signed multiplicity-loss formula is correct. |
| `UpperEdgeInventory.lean:165`, `lineEdges_pairwise_disjoint` | Edges are unordered pairs of distinct real endpoints. Two different indexed lines cannot contain both endpoints, so inventories are disjoint by geometry. Coincident lines are excluded by `NoParallel`. |
| `UpperEdgeInventory.lean:188`, `edge_cardinality` | The global inventory consists exactly of consecutive finite intersection vertices on each line. It counts bounded elementary segments, not unbounded rays. The usual `n(n-2)` budget and multiplicity correction follow. |
| `UpperElementaryEdges.lean`, `predicate_all_sides_elementary` | The weak-side certificate prevents any other arrangement line from crossing a side's relative interior. A line touching there must contain both endpoints and hence coincide with its support, which nonparallelness excludes for a different index. |
| `UpperEdgeInventory.lean:290`, `predicate_side_mem_edges` | Actual certified sides are placed on the correct support indices: `pq` on `tri.i`, `qr` on `tri.k`, and `rp` on `tri.j`. Their endpoints are actual vertices; elementarity forces consecutiveness in the sorted coordinate order. |
| `UpperTriangleIncidence.lean:196`, `exact_incidence` | Each nondegenerate triangle has exactly three distinct unordered sides. Capacity two is derived from overlap of same-side triangles, giving `3T=used+shared`. No pseudoline or abstract side-capacity substitution occurs. |
| `UpperTriangleIncidence.lean`, `certificate_incidence` | Disjoint interiors are derived from `TrianglePredicate`, `NoParallel`, and injectivity of the selected triples, using the existing `Cells` theorem. |
| `UpperSharedIncidence.lean:93`, `shared_has_nonordinary_endpoint` | The proof extracts two distinct selected triangles from an actual side fiber, aligns endpoints, and identifies the common supporting arrangement line using two-point uniqueness. |

One deliberate interface distinction matters. The generic
`UpperSharedIncidence.core_incidence` at line157 needs only disjoint triangle
interiors and a finite edge universe containing the sides. Its `D1,D2`
identity uses the algebraic partition and does not itself assume that the
triangle supports belong to `L`. The interpretation of these terms as
ordinary-to-multiple and multiple-to-multiple edges additionally uses
`predicate_indexed`, `oneCore_has_both_kinds`, `twoCore_endpoints`, and the
fact that the endpoints are arrangement vertices. All these facts are
available for the certificate application; they must not be silently attached
to an arbitrary unindexed invocation of the generic theorem.

## New core modules and remaining limitations

The source of `UpperCoreExtraction.defect_identity` restricts the loss sum
to the actual finite nonordinary core. Nonordinary vertices have multiplicity
at least three. Its `simple_arrangement_upper` additionally assumes the core
is empty and recovers the classical inequality `3T <= n(n-2)`; this is not a
new general upper bound.

The owning agent subsequently confirmed both of these CoreExtraction
theorems compiled successfully. An additional combined
`certificate_oneCore_classification` theorem is being checked to expose the
ordinary/core interpretation directly in one certificate-facing signature.

The sources of `UpperCoreLineIncidence.core_line_budget` and
`UpperCoreCombinatorics.core_edge_count` correctly derive `D2+h<=I` and
`D2<=choose(q,2)` for the actual constructed sets. The former injects path
edges into core vertices excluding the last core vertex on each used line;
the latter uses distinct two-element subsets of the actual core. Their
signatures contain no assumed global core-incidence or simple-graph budget.
At audit time their final compiler checks were pending with the owning agent;
this source review does not replace successful compilation.

The meaningful remaining gaps are:

1. Extraction of compatible cyclic fan data from the actual selected
   triangles, with the correct multiplicities, ray/endpoint uniqueness,
   positive orientation, cross-edge matching, and global degree sums.
2. The actual clean-line charging inequality `n-h<=2U+D1`.
3. Composition of those facts with the local fan theorems and the conditional
   aggregate algebra into a final restricted or unrestricted upper theorem.

`UpperFan.Sectors` and `UpperCoreBoundary.CoreFamily` explicitly package local
geometric data; they are not proved to arise from every input arrangement.
In particular, identifying their parameter `r` and their selected-ray counts
with the extracted multiplicities and global `D1,D2` is still work. Likewise,
the integer hypotheses in `UpperCoreBudget.at_most_three_multiple_points`
remain explicit. Its restricted upper polynomial is conditional at present.

Every main extraction statement here retains `NoParallel`. No reduction
from arbitrary arrangements with parallel supports, and no definition or
computation of the extremal function `K(n)`, is provided by this branch.
The identities do not require an all-cells enumeration; a future universal
upper conclusion can instead quantify over every finite certified family.

## Report wording to update

The current `upper/LOCAL_FAN_PROGRESS.md` was acknowledged by its author as
partially stale during this audit. It should mark consecutive-edge inventory,
actual multiplicities, and the defect identity as completed after their
successful logs, rather than listing them among unresolved extraction tasks.
After their pending checks pass, the same applies to `D2+h<=I`, the simple
core-edge count, and the summed multiplicity surplus. The remaining fan and
clean-line interfaces should stay explicit. The author has agreed to update
these statements and preserve the nonparallel/subset/maximum distinctions.
# Additional independent audit: clean-line matching argument

The mathematical argument in `upper/CLEAN_LINE_MATCHING.md` was checked
independently after the three final local modules were written. No flaw was
found. If one transverse line has no further positive-side intersection,
cleanliness forces all of its transverse intersections to the negative side;
this supplies the same-side existence condition for every other line. The
first such intersection gives the actual bounded elementary segment.

Under the temporary assumption that every selected segment has degree one,
the triangle at an ordinary crossing has a whole side on the clean line. Its
second transverse side enters the same half-plane, so the proved uniqueness
lemma identifies it with the selected segment at the second crossing. Thus
the triangle bases cover the crossings in pairs. Two pairs cannot share a
crossing because its selected segment would belong to two distinct triangles.
The odd cardinality `n−1` contradicts this pairing when `n` is even.

The charging count also has the stated mathematical scope: a selected edge
has an ordinary endpoint; if shared, its other endpoint is nonordinary.
At an ordinary endpoint, the charging line is uniquely the incident line
other than the edge support. An unused edge receives at most two charges,
and a one-core shared edge at most one. This argument remains valid for a
chosen finite injective subset of the triangles, with all degrees and unused
edges taken relative to that subset.

At the time of this first audit, the formal status was correctly restricted. `UpperCleanHalfplane`,
`UpperCleanEdges`, and `UpperCleanPairing` prove the actual common-side,
cardinality, segment-existence, and uniqueness ingredients. They do not yet
extract the pair cover from degree-one side occurrences or construct and
count the final global charge map. Their successful compilation alone must
not be described as a completed Lean clean-line charging theorem.

**Subsequent checked advance.** `UpperCleanCover` has now compiled and its
final signature was independently inspected: `certificate_clean_line_charge`
extracts an actual unused or one-core shared edge with an ordinary endpoint
on each clean line, under only the stated even-order, nonparallel-line,
finite-injective-family and triangle-predicate hypotheses. It closes the
pair-cover extraction described above. The remaining aggregate obligation is
the finite-fiber count over all clean lines; the local theorem does not assume
that global charging inequality.

**Final checked advance (19:11 UTC).** `UpperCleanCharging.certificate_clean_line_budget` now closes the aggregate obligation. Its independently inspected signature assumes only actual pairwise nonparallel lines, even order at least three, and a finite injective certified triangle family. The constructed map records an actual edge and its ordinary endpoint; `charge_line_unique` proves its injectivity. Unused edges contribute at most two endpoints, while `certificate_oneCore_classification` gives exactly one ordinary endpoint for each D1 edge. Thus `n-h <= 2U+D1` is now fully extracted, not a supplied hypothesis. Subset-family semantics remain valid. Together with the actual defect identity and NoConcurrent-to-empty-core bridge, `UpperEvenSimpleOptimality` proves the classical simple even upper bound. No global cyclic-fan extraction or new unrestricted nonsimple upper bound follows from these results alone.
