# Construction and obstruction experiments, 2 October 2026

This branch of the authorized three-hour session produced two substantive
results and no new finite Kobon record:

1. **Uniform 49-line seed.** A fixed rational reciprocal-slope vector on the
   actual tangent grid gives 767 cells, 47 distinguished caps, a positive
   central apex, and 24 visible exterior pairs for every 0 < ε ≤ 1/100.
   Exact independent validators passed. See `uniform-grid49/README.md` for
   the complete construction, verification, and its relation to the separate
   Lean recursion. The numerical family is inherited; the contribution here
   is an explicit compatible parameter certificate.
2. **Perfect 21-line grid obstruction.** All 236 published affine classes,
   with all 21 choices of distinguished support, are excluded from the
   prescribed saturated tangent grid whenever 0 < ε < 1/2,000,000.
   The final independent checker validates 3,765 symbolic positive dependencies
   covering all 4,956 normalizations. Arbitrary epsilon-dependent reciprocal
   slopes are included. See `grid21-obstruction/README.md` for the external
   classification assumption and the distinction between the complete exact
   computer-assisted audit and the separately Lean-proved representative.

This research record is authored by Alejandro Zarzuelo Urdiales, with
computational assistance. Existing configurations and published pseudoline
types retain their original attribution. No priority claim is made for these
observations or for the search methods.

## Bounded search results

The searches used global support/cutter subset optimization, insertion through
exact vertices, two-stage singular pivots, newly published pseudoline types,
and linear fitting to a recursive tangent grid. These are distinct from the
earlier millions of single-line local mutations.

| Experiment | Completed scope | Best result | Verification and limit |
|---|---|---:|---|
| Global deletion from the retained 49:767 witness | All 49 one-deletions and 1,176 two-deletions, then a width-60 beam | 48:721, 47:677, 46:637, 45:598 | Exact support/cutter score, adjacency, and independent direct signs. No improvement. |
| MILP deletion from 49 | One completed target; the next exhausted memory | 48:721 | Two exact checks of the saved witness. The run aborted before 47. |
| MILP deletion from 57:1045 | 90 seconds per target | 56:990, 55:939, 54:887, 53:837 | Exact incumbent checks. Timed-out incumbents do not establish optimality. |
| Chord insertion into 17:85 | All 9,180 vertex pairs; 7,136 distinct nonparallel candidate lines | 18:93 | Exact insertion score and full adjacency recount. No 18:94 candidate in this set. |
| Chord insertion into 43:587 | All 407,253 vertex pairs; 370,230 distinct nonparallel chords | 44:607 | Exact insertion score and adjacency recount. Other constructions remain possible. |
| Two-stage singular pivot from 16:72 | 12,838 first-stage candidates; 30 retained configurations, each with 29,938 second-stage candidates | 18:89 | Exact promoted-candidate recounts. Only the retained beam was explored. |
| First-hit 39-line pseudoline straightening | 94 seeded nonlinear attempts in 300 seconds | 39:353 | Best coordinates independently verified exactly. Failure does not imply nonstretchability. |
| Balanced 39-line straightening | 69 completed attempts before a rounded degenerate proposal stopped the run | 39:358 | Best exactly verified; aborted status is recorded. The script now rejects such proposals explicitly. |
| Perfect 21-line fitting with line/infinity swaps | 18 supplied representatives; 8,316 swaps and 6,916 distinct LP systems, at ε = 0 and .01 | No positive margin | Floating diagnostics only; these representatives alone do not cover every affine type. |
| Perfect 41-line first-hit type fitting | All 1,722 ordered swaps at ε = 0 | No positive margin | One supplied pseudoline type, not a complete classification. |
| Retained optimal 41:533 type fitting | 40 distinct cap-compatible systems, free infinity, ε = .001 | No positive margin | Floating diagnostics for one saved coordinate type. |
| Free-infinity 21-line fitting | All 7,560 type/line/cut combinations; 7,320 distinct triple-sign systems at ε = .01 | Four exact 21:123 realizations | Only 18 of the required 19 distinguished caps; not compatible perfect seeds. |
| Initial saturated 21-line fitting | 366 cap-compatible systems at ε = .01 and .075 | Exact obstruction for the 18 supplied representatives | Superseded in scope by the separate 236-affine-class audit. |
| Complete affine 21-line audit | 236 classes, 4,956 distinguished-support choices | All excluded on 0 < ε < 1/2,000,000 | Exact polynomial certificates and independent coverage; external enumeration completeness is attributed. |
| Retained 49:767 affine-type fitting | All 49 supports at ε = .001, .00001, .01, .03, then at ε = 0 | 100 exact positive-ε fits; 25 feasible limit systems | Led to the fixed-slope uniform certificate, not a new triangle count. |

The deletion reports use `baseline` for the universal formula G, not the
strongest retained finite envelope. For example, 46:637 and 45:598 remain
below the retained 667 and 645. No below-target candidate was promoted to
the main finite certificate catalog.

The early free-projective 49-line screen was intentionally stopped after
its first fits showed only 743 affine cells despite 47 distinguished caps.
Its saved midpoint files are exact diagnostics; it is not a completed scan.
The affine screen preserves the signs involving the original infinity line
and is the source of the successful uniform 767-cell seed.

## Exactness and positive controls

The independent angle/distance implementation recovers exact 9:21 and 15:65
arrangements from published words on its first attempts. The line/infinity
grid fit recovers six exact 9:21 arrangements. Its projective sign formula
was checked against 90 actual rational coordinate transformations. Separate
free-chart controls validate 72 nine-line charts and 420 twenty-one-line
charts against exact geometric transformations and cell adjacency.

Promoted coordinate files are checked by `research/kobon-hybrid/exact_geometry.py`
(vertex adjacency) and `verify_direct.py` (independent direct signs). The
chord scans also have a specialized exact scorer and rational controls.
Floating LP margins, nonlinear losses and infeasibility statuses are never
treated as proofs. The final obstruction and uniform-seed validators use only
Python integers and fractions. Their separate Lean status is recorded in
the session's formalization report.

## Primary sources and reproducibility

* Roman Parpalak and Denis Utkin,
  [Enumeration and Classification of Triangle-Maximal Pseudoline Arrangements](https://arxiv.org/abs/2607.29236),
  2026. The 21-line classification has 236 affine Euclidean classes; its 18
  projective classes include infinity in a 22-support closure. Larger first-hit
  words describe pseudolines and do not prove straight-line realizability.
* Input URLs, hashes and the pinned commit
  `a9c628cbaa765935f224ed5ca5fde7b2f591e16d` are in
  `primary-inputs/manifest.json`. `primary-inputs/README.md` explains the
  provenance and the data-license scope found in that commit.
* Pavlo Savchuk,
  [Improving the Lower Bounds for the Kobon Triangle Problem](https://arxiv.org/abs/2507.07951),
  2025, motivates angle/distance hinge straightening. The implementation here
  is independent; published source code was not copied.
* [OEIS A006066](https://oeis.org/A006066) was checked during the session.
  Pseudoline counts were never reported as straight-line lower bounds.

Scripts are in `experiments/2026-10-02/`. Discovery package versions used with
Python 3.12.14 are recorded in [requirements-discovery.txt](../requirements-discovery.txt);
they can be installed in an ordinary virtual environment. The optional local
`work/*-deps` lookup paths do not prevent normal installed-package resolution.
Exact validators need only standard Python. Optional
python-flint accelerates symbolic production but is not used by the final
obstruction checker. The default deterministic seed is 20261002. Reports
record the actual input, parameters and completed scope, including aborted
or intentionally stopped searches.

## Remaining research directions

1. Complete the Lean import of the full finite obstruction dataset and its
   affine-type coverage. The exact independent audit is already complete.
2. A perfect 21-line recursive seed requires departure from the obstructed
   small-epsilon tangent-grid ansatz. Merely allowing epsilon-dependent or
   diverging slopes is already covered by the obstruction.
3. Nonuniform intercept grids and recursions that renormalize epsilon remain
   distinct possibilities. Neither was ruled out or exhaustively searched.
4. The successful 49-line uniform seed offers a concrete formalization target
   for optimal odd and simple-even BBL families. The formulas themselves are
   inherited numerical constructions; formal scope must follow the actual
   compiled theorem, not the numerical experiment alone.
5. Singular configurations from other 17-line or 43-line types remain possible.
   Exhaustive chord scans of two fixed sources are not global impossibility
   results.
