# Extension and family claim audit

Prepared for the comprehensive paper dated 22 September 2026. Author of the
paper: **Alejandro Zarzuelo Urdiales**. This audit records the exact scope of
the two sections `extensions.tex` and `families.tex`; it does not enlarge the
claims of the frozen Lean release. The inherited mathematical constructions
retain their published attribution.

## Status vocabulary

- **Lean, geometric:** an actual real-coordinate construction or geometric
  theorem is proved, with standard Lean logical axioms only unless explicitly
  marked otherwise.
- **Lean, arithmetic/interface:** a counting theorem is checked with stated
  abstract hypotheses; this does not certify an unproved geometric bridge.
- **Ordinary theorem:** a mathematical argument is supplied, but its full
  geometry is not yet connected end to end in Lean.
- **Published-theorem consequence:** the deduction uses an attributed
  published construction in addition to the locally checked seed/arithmetic.
- **Conditional:** the displayed hypothesis is not silently discharged by
  finite examples or separately proved components.
- **Exact finite evidence:** rational coordinates and specified independent
  counters; distinguish this from a Lean certificate.
- **Partial:** a required verification step was interrupted or remains open.

## Extension claims

| Paper label / claim | Exact mathematical scope | Verification status | Primary local evidence | Attribution / limitations |
|---|---|---|---|---|
| `ext:march` | Proposed `K(2m+2) >= K(2m+1)+m` | **Unproved in the archived March source** | `archive/2026-03-original/kobon_triangles_paper.tex`; archived `KobonTriangles.lean` | March proposal is Zarzuelo's; eight archived `sorry` placeholders, including the main extension. Archive is excluded from the active library. |
| `ext:realization` | A simple arrangement, duplicate-free old triangle list, duplicate-free visible-pair list, admissible normal, and a height beyond all old vertices give a simple exterior extension with the sum of both list counts | **Lean, geometric** | `Kobon/Exterior.lean`, `Exterior.extension`, `safeHeight_beyond` | No parity restriction; does not assert that at least `floor(n/2)` visible pairs always exist. Exterior addition has BBL/Blanc precedents. |
| `ext:charging`, `ext:average` | `b>=max(3,n-d)`, cyclic profile sum `(n-1)b`, exact exterior capacity and averaged lower bound | **Ordinary geometry plus Lean counting core** | `research/kobon-extension/manuscript.md`; `BoundaryExtension.lean` and current boundary modules | Universal Euclidean ray/unused-edge charging and cyclic-realization bridges are not claimed fully formalized. |
| `ext:defect-theorem` | `Ks(n+1)>=T+ceil((n-1)/(2n)*max(3,3T-n(n-3)))` from a simple `n`-line witness | **Ordinary theorem; not end-to-end Lean** | Same manuscript; `Exterior.extension` supplies the independently verified realization step | Can be iterated as an ordinary theorem; quantitative-priority claim remains unresolved. Do not feed a nonsimple classical witness into it. |
| `ext:odd-full` | Defect at most two at odd order gives an exterior gain exactly `(n-1)/2` | **Ordinary theorem plus checked finite counting implication** | Same manuscript and cyclic core | Applies to every simple odd arrangement attaining the segment-count bound, not to every odd maximum without that hypothesis. |
| `ext:budget` | Exterior chains satisfy `b_(r+1)+c_r<=b_r+2`; hence cumulative gain is at most `b_0+2r-3` | **Ordinary geometric budget; Lean arithmetic contradiction** | `research/successor-formalization/README.md`; `Kobon/Iteration.lean` | Rules out indefinite full-gain exterior chains, not the recurrence for maxima using reconstruction or interior insertions. |
| `ext:49-table` | One exact chain `49:767 -> 50:791 -> 51:814 -> 52:816 -> 53:818`, capacities `24,23,2,2,2` | **Exact coordinate/profile audit plus Lean finite profile arithmetic** | `experiments/2026-09-20/successor-49/chain.json`; `Kobon/Iteration49.lean` | Coordinate-to-profile identification is exact Python; profile maxima are kernel checked. These capacities are not maximum-function upper bounds. |
| Two-step 49 obstruction | From 47 wedges, gains 24 and 25 would leave at most two wedges | **Checked arithmetic under the ordinary wedge budget** | `two_steps_49_obstruction` | Stronger than failure of one greedy tie break, but restricted to exterior extensions of the stated seed. |
| `ext:conditional-closed` | Given `F(n+1)>=F(n)+floor(n/2)`, sum to `F(s)+floor((n-1)^2/4)-floor((s-1)^2/4)` | **Lean, arithmetic, conditional** | `Kobon/Iteration.lean`, explicit `FullStepClaim` hypothesis | The arithmetic theorem does not prove the geometric recurrence. |
| `ext:49-unconditional` | `K(n)>=floor((n-1)^2/4)+191` for every `n>=49` | **Lean, unconditional geometric lower bound** | `AllN.from_49_unconditional`; `research/all-n-formalization/README.md` | Obtained from finite 49/50 witnesses and the all-order baseline; does not construct a nested successor chain. |

## Family claims

| Paper label / claim | Exact mathematical scope | Verification status | Primary local evidence | Attribution / limitations |
|---|---|---|---|---|
| `fam:doubling` | `q=4r>=20`, `0<epsilon<tan(pi/(2q))`, actual simple old graph arrangement on the prescribed grid, all `q-1` distinguished triangles, positive central apex, `T` distinct certified old triangles imply an actual simple `2q+1`-line arrangement with at least `T+q^2` triangles | **Lean, geometric, standard axioms** | `Kobon/BBLDoubling.lean`, `BBLDoubling.doubling` | No assumed future crossing order or triangle-retention premise. Does not return the full recursive seed invariant. BBL owns doubling and its numerical gain; this work supplies a formal geometric proof with a qualitative two-scale realization. |
| `fam:crossing`–`fam:displacement` | Exact new-line intersection and perturbation identities, exceptional complements, realized finite row order | **Lean, geometric/analytic, standard axioms** | `BBLIntersection`, `BBLGrid`, `BBLPencilLimits`, `BBLPencilProfiles`, `BBLPencilRegularity`, `BBLRealization`, `BBLRealizedPencil` | Choose delta small first and kappa small afterward. These are actual real-line theorems, not merely simulations of crossing keys. |
| `fam:mixed-count` | At least `q^2` mixed triples; each is an actual empty triangle once realized | **Lean, counting and geometry** | `BBLCount`, `BBLRowGeometry`, `BBLTriangles` | Auxiliary row keys are comparison data, not physical coordinates. Realization is separately discharged in the one-step theorem. |
| Old cap replacement and retention | All old counted triangles survive or are replaced one for one, disjoint from the mixed list | **Lean, geometric** | `BBLAlternation`, `BBLCapEnvelope`, `BBLCapBridge`, `BBLCentralPersistence`, `BBLCapRetention`, `BBLOldRetention`, `BBLAssembly` | Saturation and central orientation are actual input hypotheses; general old triangle persistence alone would not suffice for triangles on `Y0`. |
| `fam:seed11-slopes`–`fam:seed11-grid` | True tangent-grid 11-line seed, every `0<epsilon<=10^-5`, 32 triangles, nine distinguished triangles, five visible pairs | **Lean, parametric geometry with checked finite boxes** | `Parametric`, `TangentBounds`, `SeedFamily`, `HybridBoundary`; `research/kobon-hybrid/` | Count32 is inherited from the Honma-based seed in Savchuk. Compatible realization and uniform parameter verification are the new local contribution; not a new 11-line numerical maximum. |
| `fam:eleven-family` | `q=10*2^t`, odd order `q+1`, at least `(q^2-4)/3` triangles | **Published-theorem consequence; recurrence arithmetic checked; infinite geometric Lean iteration incomplete** | `research/kobon-hybrid/manuscript.md`; BBL Proposition3.1 and Remark3.2; family arithmetic modules | Epsilon depends on the finite target depth. The q=10 initial doubling is outside the current q>=20 formal theorem. No single fixed positive epsilon is asserted for infinitely many steps. Priority not established. |
| `fam:even-defect` | Same q, even order `q+2`, at least `(q^2-4)/3+q/2-1` | **Published odd-family consequence plus ordinary boundary-defect theorem** | Hybrid and extension manuscripts | Not an end-to-end Lean infinite even theorem. Two below the displayed simple polynomial upper; not necessarily a record. |
| `fam:even-conditional` | Full gain `q/2` at every family member provided that many visible pairs exist at each stage | **Conditional theorem** | `research/six-hour-2026-09-21/hybrid-family/boundary-invariant.md`; `BBLVisible`, `BBLVisibleAssembly`, `BBLCentral`, `BBLPersistence` | Detailed ordinary working proof and many formal components exist. Remaining rightmost-line/old-vertex comparison and recursive assembly are not replaced by the finite checkpoints. Paper intentionally does not label this an unconditional completed Lean family. |
| `fam:finite-table`, rows through161/162 | Exact family checkpoints with full finite even gain `q/2` | **Active finite Lean witnesses and independent exact counts** | `research/kobon-hybrid/`; frozen certificate index/manifest | At22 and42 stronger known values143 and553 already exist. Finite table is a family table, not a best-known table. |
| 321:34132;322:34292;641:136532 | Simple exact rational arrangements with these counts | **Two independent exact counters; outside routine Lean catalogue** | `experiments/2026-09-21/hybrid-family/n321.json`, `n322.json`, `n641.json`; `larger-members-verification.json` | Large files use rational components up to916/985/1103digits. No Lean or numerical-priority claim for these experimental certificates. |
| 642:136852 | Generated coordinates, simplicity and adjacency count passed | **Partial** | `n642.json`; `large-run-status.json` in the same experiment directory | Independent direct counter interrupted. Not a completed dual-counter certificate; not promoted into Lean catalogue. |
| `fam:tamura` | Known odd family q=`4*2^t`, count `(q^2-1)/3`, and even companion adding `q/2` | **Published/classical family; finite members independently formalized** | `TamuraSeed5`; `generate_tamura_family.py`; finite certificates through129/130 | Numerical family is known. Whole-parameter five-line seed is checked. Small q4/8/16 are outside `BBLDoubling.doubling`; unfinished true-parametric `TamuraSeed33` draft is excluded from completed results. |
| `fam:pu` | PU odd family q=`18*2^t`, count `q^2/3-1` | **Published Parpalak–Utkin theorem; local independent seed reproduction** | `prior-seed19-interval.json`, `prior-seed19-rational.json`; arXiv2604.22035 | Seed checked on `0<epsilon<=10^-3`,1632endpoint checks,107triangles,17caps. This interval reproduction is not a new all-family Lean theorem. BBL's older q18 family was pseudoline, not straight-line. |
| PU simple even corollary | `q^2/3+q/2-1` at q+2, q=`18*2^t` | **Attributed consequence of PU input and ordinary defect-two extension** | Extension manuscript | Correct odd expression is `q^2/3-1`; `(q^2-1)/3` would be nonintegral for these q. Values20:116,38:449,74:1763,146:6983. Nonsimple published20:117and38:450 concern classical K. |
| `fam:21-target` | Proposed recursive Lean family q=`20*2^t`, count `(q^2-4)/3` | **Integration target, not existing completed declaration** | `BBLSeed21`, `BBLGridReindex`, `BBLNextSaturation`, `NEXT_ITERATION_PLAN.md` | Numerically the tail of the paper-supported11-seed family. Needs complete witness transport and parameter induction. |

## Exact remaining recursive obligations

1. Strengthen the one-step conclusion to return coordinates/slopes, a nodup
   witness list, and all next-seed data, rather than only `SimpleLowerBound`.
2. Include central retention in the finite intersection of eventual conditions
   independently of whether the input counted list contains that triangle.
3. Transport all support triples through the full sorting permutation, including
   all six support orders, and prove length and nodup preservation.
4. Identify the reindexed graph equations using the proved cut identities.
   Reuse the proved simplicity pullbacks and next-grid saturation.
5. Normalize the verified21 seed's grouped source labels. Its ordered
   nonhorizontal source list is
   `[11,1,12,2,13,3,14,4,15,5,6,16,7,17,8,18,9,19,10,20]`;
   the central source lines5and6 have apex height`5*epsilon/2`.
6. Induct on `exists eta>0, forall 0<epsilon<eta, exists a compatible seed`.
   Slopes, delta and kappa may depend on epsilon. Shrink eta below the next
   half-grid gap; do not require one positive epsilon to work at every depth.
7. For the stronger even family, additionally assemble the visibility count,
   compare the central new intersection on the old rightmost line with every
   old vertex, transfer x-order to the fixed normal, and preserve the
   rightmost-line invariant. Triangle saturation alone does not imply this.

Central orientation needs **no new limiting sign estimate** after reindexing:
the next central apex is exactly the old central apex. The issue is retaining
and transporting its witness, not proving that positivity survives a moving
point. The epsilon quantifier does need the uniform small-parameter form above.

## Negative search evidence and exclusions

- Compatible21 search:11,547,910floating proposals over a one-hour run, best132,
  no133candidate and hence no new exact candidate accepted. This is not a
  nonexistence proof.
- Compatible21 transfer:3,234LP attempts (462ordered chart/support choices,
  epsilon0plus six positive scales), no strict feasible margin. This excludes
  no arrangement beyond the tested numerical formulation.
- Reproducing existing counts and expanding a local certificate catalogue does
  not establish first discovery. In particular, OEIS attribution at28,30,34
  must be distinguished from older matching consequences at30and34.
- No simple-arrangement upper bound is applied to unrestricted classical K.
- No pseudoline construction is used as a straight-line witness without a
  realization theorem.
- No finite table or finite numerical search is used to infer an infinite
  construction theorem.

## Files owned by this contribution

- `paper/sections/extensions.tex`: March proposal, verified exterior geometry,
  ordinary defect theorem, parity criteria, exterior budget,49chain and the
  conditional/unconditional distinction.
- `paper/sections/families.tex`: complete one-step BBL statement/proof outline,
  seed11, even companions, finite checkpoints, classical/PU attribution and
  the precise recursive formalization plan.
- This audit. Figures are produced by the construction-search branch; the
  bibliography and surrounding sections are integrated by the parent task.
