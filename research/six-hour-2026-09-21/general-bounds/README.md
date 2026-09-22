# General bounds, multiplicity geometry, and independent source audits

This folder records one workstream of the research session, originally allocated six hours and then shortened to three hours. It separates proved Lean components, paper-level geometric arguments, exact finite verification, external constructions and unsuccessful searches. No result here is an unrestricted solution of the Kobon problem.

## Read these first

* [Lower-bound priority audit](lower-bound-priority-audit.md): Füredi–Palásti already supplies an all-n quadratic construction. The session's stronger affine formula is attributed as an explicit refinement and Lean formalization; first numerical priority is not established.
* [Upper-bound scope audit](upper-bound-scope-audit.md) and [3–60 source table](upper-scope-table.md): the even-order BBL and Blanc theorems require simple arrangements. The weaker Clément–Bader classical envelope is kept as a reported external theorem with a local proof-wording issue noted.
* [Multiplicity budget](multiplicity-budget.md): exact elementary-segment accounting, including parallel-pair corrections and the distinction between ordinary and multiple endpoints.
* [Clean-line parity and fan argument](clean-line-parity.md): restricted nonsimple upper theorems, their full paper derivations, and precise remaining formalization obligations.

## Mathematical progress

For an even number n>=4 of pairwise nonparallel lines, write T for its bounded triangular faces, `delta=n(n-2)-3T`, and t_r for its number of finite r-fold points. The paper-level geometric argument gives

`2 delta >= n + sum_{r>=3}(2r²-11r+6)t_r`.

In particular, if every finite multiple point has multiplicity at least five, the arrangement satisfies the same even polynomial upper bound as Blanc's simple theorem:

`T <= floor(n(n-5/2)/3)`.

A separate sharper local fan count for at most two finite multiple points, of any multiplicity, gives

`T <= floor(n(n-5/2)/3)+1`.

Both statements require **no parallel pairs**. Their priority is unestablished, and the full all-arrangement upper proof is not yet encoded in Lean. The actual fan obstruction, its cyclic count, and the conditional arithmetic are encoded:

| Module | What is proved |
|---|---|
| `Kobon/FanGeometry.lean` | Actual real triangle supports propagate across ordinary endpoints; a fan strip cannot connect opposite radial rays. |
| `Kobon/FanCount.lean` | Exact cyclic double count: a subset of 2r rays with no run of r-1 has at most2r-3 elements. |
| `Kobon/CyclicFan.lean` | Actual antipodal radial geometry and adjacent triangular sectors imply the no-long-run property and therefore the2r-3 bound. |
| `Kobon/CleanLineBudget.lean` | Nine arithmetic consequences with all remaining incidence, charging and core hypotheses explicit. |
| `Kobon/SharedFan.lean` | Six actual certified triangles around a triple point have six distinct elementary radial sides, each shared by two triangles. |

All five modules compiled with Lean4.31.0. Printed theorem axiom sets are limited to `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` declarations or custom axioms in these modules. Remaining global work is to extract cyclic sector data and elementary segments from arbitrary finite arrangements and formalize the clean-line charging argument.

The consolidated successful build is saved in [lean-build.log](lean-build.log), and the final seventeen-theorem dependency audit is saved in [lean-axioms.log](lean-axioms.log). Reproduce the latter with `lake env lean experiments/2026-09-21/general-bounds/audit_general_bounds.lean` after building the five modules.

The exact geometric audit passed597 arrangements (97 retained certificates,300 deterministic random arrangements,200 two-pencil examples), then25 additional current external witnesses. These computations support the paper argument without replacing its general proof.

## New independent checks of existing constructions

[Maiorana14](maiorana14/INDEPENDENT-REVIEW.md) contains all fifteen published exact54-triangle witnesses, with full CC-BY4.0 attribution and immutable commit provenance. Our two independent counters agree on their complete triangle sets. Fourteen have two triple points; one has four. Their lower bound remains attributed to **Andrea Maiorana**.

[Current Parpalak–Utkin gallery](parpalak-utkin-current/INDEPENDENT-REVIEW.md) contains independently verified certificates at8:15,14:54,20:117,26:204,32:315,36:402,38:450,42:553,46:667 and50:792. These are external records, some missing from this repository's older finite coordinate catalog. The classical eight-line result has older discovery priority; the gallery is the coordinate source.

The local smoothing idea was decisively tested. All four simple resolutions of Maiorana's two-triple54-triangle seed have52,52,53,52 triangles. For the PU collinear-core examples, all local choices are independently realizable by private-line offsets, but the best nearby simple counts are14,51,114,203,313,448 and791 at orders8,14,20,26,32,38 and50. Thus both universal nondecreasing smoothing and a universal collinear-core loss-at-most-one shortcut fail. These are exact finite negative results; see `collinear-resolution-model.json` and `parpalak-utkin-current/all-local-resolutions.json`.

The previously published19-line compatible seed was independently interval-checked over `0<epsilon<=1/1000`:1632 exact endpoint determinant checks, a107-triangle rational witness and all17 distinguished-line caps. See `prior-seed19-interval.json` and `prior-seed19-rational.json`. The seed and the18·2^t+1 series retain Parpalak–Utkin attribution; this work adds a reproducible independent check.

## Search directions and negative results

The [experiment register](experiment-register.md) identifies scripts, saved outputs, exactness boundaries and reasons to pivot. The principal attempted alternatives were nonuniform nodal cubics, real elliptic torsion groups, concurrent FP resolutions, Fourier support-function deformation, partial BBL deletion, fixed tangent-grid realization by LP/MILP, and singular-boundary searches near the44-line optimum for simple arrangements.

These alternatives have not yet improved the retained bounds. Their failures are local or finite search evidence, not impossibility theorems. Exact SMT chart obstructions on fixed cubic seeds are recorded by the construction-search workstream and are stronger than unsuccessful numerical chart sampling, but still concern those fixed configurations only.

## Best next steps

1. Finish the global arrangement-to-fan and clean-line charging formalization. The local geometric modules now provide useful proved building blocks.
2. Seek a multiplicity-aware parity argument controlling many triple and quadruple points. High multiplicities already have positive weight; triples and quadruples are the difficult part of the current budget.
3. Preserve singular strata in future lower-bound searches. Classical records exceed simple bounds, and smoothing can lose several triangles even when all resolution choices are freely realizable.
4. Search different projective topologies or jointly optimize charts and geometry. The tested elliptic and local cubic seeds have genuine fixed-chart obstructions.
5. Complete numerical priority review before claiming the all-n affine formula is first in the literature. Its Lean construction and explicit affine chart argument are established deliverables independent of that historical question.
