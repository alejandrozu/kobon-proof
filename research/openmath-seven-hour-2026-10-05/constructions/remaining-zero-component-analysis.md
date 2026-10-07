# Remaining component equality cases — mathematical analysis

Recorded 2026-10-06, after the source-free N12 gain and the actual N13/A0 support-extreme proof. This is a scoped analysis, **not a new Lean theorem**. No active Lean source was changed.

Assume an actual injective selected-triangle certificate, `NoParallel`, all core support cardinalities equal to three, and a finite nonempty shared-core-closed set P contained in the cores. Write H for its `componentCost`; a,d,m for ordinary degree, core degree and marked count; A for its unmarked full (2,4,0) cores; F for the number of full (1,5) cores; E,D,R for the numbers of (a=3), (2,1), and (1,2) cores. Let B be the poor set a≤1,a+d≤2. Define x=0 on full a+d=6 cores and x=degreeFrom(A,p) otherwise.

## Exact equality decomposition

Let W(p)=6−2a(p)−d(p), u(p)=unpaidWeight(a,d,m), and

s(p)=W(p)+u(p)+2m(p)−2d(p)·1_B(p)+2x(p)·1_B(p)
      −3·1_E(p)−3·1_D(p)−1_R(p)−x(p).

The actual no-double N13 result makes the old J13 correction empty. The proof of `finite_n12_curvature_gain` supplies s(p)≥0. Define

Ccap=Σ_B d−Σ_P m−Σ_B x,   Ccone=Σ_P x−2|A|.

Actual marked/cross capacity and cone incidence give Ccap,Ccone≥0. The point sum and the closed curvature identity give the **exact algebraic identity**

2H+F−3E−3D−R = Σ_P s + 2Ccap + Ccone.

For H=F=0, the source-free bound first forces E=D=R=0. The identity then forces Ccap=Ccone=0 and every s(p)=0. This needs an explicit equality-decomposition lemma before being cited as a Lean result; it follows from the displayed proof algebra but has not been added to active sources.

## Poor saturation is derivable, with the necessary intermediate step

Actual low-cap vertices have m=0. For poor vertices the point gap is

s=6−2a−3d+x.

Its five possible poor cases are:

| (a,d) | s |
|---|---|
| (0,0) | 6+x |
| (0,1) | 3+x |
| (0,2) | x |
| (1,0) | 4+x |
| (1,1) | 1+x |

Thus point-gap equality forces every poor vertex to be (0,2) with x=0. In particular Σ_B x=0. **Only now** Ccap=0 yields the old `TightOn` equality Σ_P m=Σ_B d. Combined aggregate saturation alone would not justify this conclusion.

The compiled `UpperOpenMathMarkedPorts.tight_marked_edge_coverage` can then be applied: every incident shared-core edge at each poor target is actually marked at its other source. This is the required geometric coverage statement, rather than an unsupported per-target inference. `marked_poor_antipodal_neighbor` supplies the other shared-core neighbor on the opposite ray. Shared-core closure retains both neighbors in P. Consequently such a poor (0,2) vertex cannot maximize an affine functional injective on P.

## Remaining point profiles

With H=F=0, the zero point gap leaves:

| (a,d,m,x) | status |
|---|---|
| (0,2,0,0) | marked-saturated poor; opposite shared-core pair |
| (0,4,0,2) | R04; four shared core rays contain an antipodal pair |
| (0,6,0,0) | full; antipodal core pair |
| (1,3,0,1) | N13 with an A0 neighbor; actual support-extreme exclusion now compiled |
| (2,2,0,0) | unmarked balanced R22; the remaining possible exposed type |
| (2,2,1,2) | excluded by the new actual local-port budget m+degreeFrom(A0,p)≤d, reported FULL PASS Std by the parent team |
| (2,4,0,0) | A0 full; antipodal core pair |
| (2,4,1,0) | marked full; four shared core rays contain an antipodal pair |

The per-source m+x≤d step is justified mathematically by disjoint incident inventories: a marked edge from a nonfull source goes to a poor target with a≤1, whereas an edge counted by x goes to an A0 target with a=2. Their union lies inside the d incident shared-core edges. The parent team subsequently proved the actual LocalPortBudget statement with standard axioms and is handling its promotion/replay. Thus the marked-R22 row is now excluded by a separate verified local restriction, rather than silently omitted from the finite relaxation.

The full and R04 opposite-pair maximum exclusions use the finite fact that four rays among six contain a pair separated by three; actual shared-core closure retains the two endpoints. Together with the poor and N13 exclusions, an injective-affine maximum of a hypothetical zero-cost, F-free component must be an unmarked balanced R22.

## Precise remaining geometric target

The old `PaidZeroTypes`/`PaidZeroRigidity` proof does not apply unchanged: even after TightOn is recovered, its six-type classification excludes the new N13(x=1) and R04(x=2) profiles.

The decisive localized extension is:

> In an actual closed zero-gap component of the above types, an injective-affine maximum p of unmarked balanced type (2,2,0) cannot have a shared-core neighbor q of type N13 with x=1 or R04 with x=2.

This is two concrete matched-chart cases, R22→N13 and R22→R04, with the actual A0 neighbor(s) extracted at q. A useful constructive conclusion would be a core y in the same component with affineEval(y)>affineEval(p), or a strict convex representation of p by component cores.

Once those cases are excluded at the maximum, poor neighbors are excluded by `unmarked_target_not_poor` and recovered TightOn. Its two neighbors would therefore be rigid R22 or full. This restores the local classification required by `certificate_normalized_neighbor_not_full`. The remaining R22/R22 core-triangle closure can use the existing actual matching and `three_two_cap_fans_incompatible` / `certificate_closed_two_two_impossible` machinery.

**Current limitation:** knowing that q itself is not a maximum does not exclude q being adjacent to the maximum p. The newly proved N13 escape therefore cannot be substituted for the missing R22→N13 coupling argument. No contradiction for the boundary R22 cases and no unconditional additive-per-component defect gain is claimed here.

## A further source-side equality reduction

Cone equality can also sharpen the actual boundary diagrams, but requires its own sum-of-nonnegative-gaps derivation. For each A0 source s in P, let t(s) be its number of nonfull shared-core neighbors. The already proved full-neighbor-pair obstruction gives at least one nonfull tip in each of its two disjoint adjacent-core pairs, hence t(s)≥2. Actual cross-edge double counting gives Σ_s∈A t(s)=Σ_P x. Therefore Ccone=0 implies Σ_s(t(s)−2)=0 and **t(s)=2 for every A0 source**, using the pointwise lower bound. There is exactly one full and one nonfull tip in each adjacent-core pair; this is not inferred from aggregate cone capacity alone.

In particular, across an A0–nonfull core side, the adjacent outer core in that A0 fan must be full. In the endpoint-ordinary N13 orientations, actual matching can identify this adjacent core with the R22 source's other shared-core neighbor. This would reduce that subcase to a specific R22–N13–full core triangle with an A0 attached across the N13/full cap. Interior-ordinary N13 orientations need a separate extraction: the R22 source's other core can correspond to an unshared target ray, so that identification must not be assumed universally. Neither subcase has been excluded here. The old normalized-full exclusion assumes the R22 source's other neighbor is rigid or full, whereas here it is N13.

The corresponding R22→R04(x=2) contact has two actual A0 incidences at the R04 tip. Each can be constrained by the same saturated adjacent-cap rule. The next proof should enumerate these matched port positions and force either an illegal full pair, a fourth supporting line at a triple tip, or a core beyond the affine maximum. No such exclusion has been established in the present run.

Notation matching the root equality audit: Dgain=2H+B15−3E3−3P21−N12, Rcap=Σpoor d−Σm−Σpoor x, Ccone=Σx−2A. The identity above is exactly Dgain=Σs+2Rcap+Ccone. This equality decomposition and its zero-case classification are mathematical analysis, not separately Lean formalized statements.


