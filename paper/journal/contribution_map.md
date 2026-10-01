# Contribution map for the journal version

Editorial supplement prepared 1 October 2026. This is a coverage
map, not part of the journal manuscript and not a new mathematical audit. It
maps the preserved 60-page manuscript and its frozen mathematical release to a
separate article of at most 15 pages, including references. The full manuscript,
its appendices, its figures, and its source evidence remain unchanged.

**Final coverage review:** all C1-C16 are represented in the completed
13-page article, including its 17 references. Four figures fit without
reducing the 11-point text: affine chart, normalized deficit, exterior
resource, and shared fan. The first three recommended figures below are
therefore retained together with the normalized-deficit plot.

The exact 81/161 projective-face census was independently replayed during
this editorial audit: affine and projective counts are respectively 2132
and 8532. Reproduction uses projective_faces in
experiments/2026-09-20/chart_search.py, with arrangement/read_lines in that
directory's research.py, on research/kobon-hybrid/certificates/n081.json and
n161.json. It establishes a chart obstruction only for these fixed inputs.

## Editorial claim and evidence policy

The journal article's central contribution is an explicit, fully formalized
affine refinement of the Füredi–Palásti construction, together with geometric
extension and doubling interfaces, compatible parameter families, and
multiplicity-sensitive upper-bound ingredients. A complete formalization is a
different claim from first numerical discovery. The audit does not establish
first numerical priority for the affine formula, the restricted upper
consequences, or the finite counts.

Keep four evidence levels visible at the relevant statements:

- **General Lean theorem:** actual real geometry proved for arbitrary permitted
  parameters, using the standard logical axioms.
- **Finite Lean certificate:** exact coordinates and triangle lists; native
  evaluation is recorded where used.
- **Ordinary mathematical argument:** the long paper supplies a geometric proof,
  but its global arrangement-to-combinatorics bridge is not fully encoded.
- **Conditional or computational result:** hypotheses or finite solver/search
  scope remain explicit; neither is promoted to a general geometric theorem.

“Retain all novelty” should mean retaining each distinct mathematical
contribution and its status, not reproducing every checkpoint, rendering,
auxiliary declaration, or failed proposal count. No short-paper statement should
claim that there was previously no all-order bound, that an omitted OEIS entry
was new, or that this project solved the unrestricted Kobon problem.

## Essential contribution-to-section map

Planned section names below are descriptive; final numbering may change.

| ID | Full-paper result and source | What the journal version must retain | Planned short section | Contribution and inherited material |
|---|---|---|---|---|
| C1 | `geometry.tex`, certificate soundness and Theorem `thm:certificate-cell`; `Geometry`, `Euclidean`, `Cells`, `Simple` | Define the exact sign certificate; state that valid sorted triples give nondegenerate bounded triangular cells with nonempty, pairwise disjoint interiors. Give the sign-cell proof in compressed form. | Definitions and proof interface | Reusable geometric formalization and semantic bridge. Line arrangements, determinants, and strict sign cells are inherited mathematics; no first-formalization priority claim is needed. |
| C2 | `universal.tex`, `thm:main`, `lem:shifted-count`, `lem:one-cap`, `lem:two-caps`; `Universal.baseline_sound` | State the full all-natural-order formula, including small cases. Retain the shifted repeated-index count, projective covariance, cap exposure, additional triples, and simplicity. | Uniform construction | Explicit affine refinement and complete real-coordinate Lean proof. The trigonometric family belongs to Füredi–Palásti; first numerical priority for the displayed affine function remains unestablished. |
| C3 | `universal.tex`, `cor:gain` and `eq:gap`; `Universal.baseline_improvement` | Give residue gains `(1,1,0,2,0,1)` and the exact distance to the Tamura polynomial. Say explicitly that the gain is constant and that stronger special families exist. | Uniform construction, final paragraph | Exact comparison of the new formal guarantee with an established formula. Not a new asymptotic coefficient or a universal numerical SOTA claim. |
| C4 | `finite_results.tex`, `prop:envelope`; `Universal.all_n` | Define the maximum with the saved finite catalog and state its soundness. Distinguish simple and nonsimple witnesses. Retain one compact table and the data link. | Finite consequences and verification | Verified aggregation and reproducibility; taking a maximum is elementary. Imported records, older odd inputs, and known dyadic families retain their attribution. |
| C5 | `extensions.tex`, `ext:realization`; `Exterior.extension` | State actual exterior-line existence from a certified visible-pair list, with preservation of old triangles and simplicity. Explain that the supply of enough pairs is a separate hypothesis. | Extension and its limits | Completed geometric Lean interface. Exterior addition itself has precedents; this is not an unrestricted successor recurrence. |
| C6 | `extensions.tex`, `ext:charging`, `ext:defect-theorem`, `ext:odd-full` | Retain the explicit all-parity quantitative gain `ceil((n−1) max{3,3T−n(n−3)}/(2n))`, the wedge/defect charging argument, and the full-gain consequence for odd simple inputs of defect at most two. | Extension and its limits | Quantitative formulation and certificate connection. Global boundary charging and Euclidean-to-cyclic extraction remain ordinary manuscript geometry; their arithmetic and local realization components are formal. First priority is not claimed. |
| C7 | `extensions.tex`, `ext:budget`, `ext:49-table`; `Iteration.no_infinite_full_gain_budget` | Keep the resource inequality `b_next + gain ≤ b + 2`, its linear cumulative bound, and the exact 49-line test. State that two exterior gains 24 and 25 from the recorded 49:767 seed would violate the wedge budget. | Extension and its limits | Structural limitation of repeated exterior addition, with checked arithmetic and an exact finite example. It does not refute a recurrence for maxima, interior insertion, or reconstruction between steps. |
| C8 | `extensions.tex`, `ext:49-unconditional`; `AllN.from_49_unconditional` | Preserve the concise unconditional target `K(n) ≥ floor((n−1)²/4)+191` for `n≥49`, while saying it follows from separate constructions rather than a nested chain. | Extension and its limits, short corollary | Answers the original numerical target with a complete theorem. The summation identity alone is not a geometric construction; the target is weaker than the current retained all-order function. |
| C9 | `families.tex`, `fam:seed11-slopes`, `fam:seed11-grid`; `SeedFamily`, `Parametric`, `TangentBounds` | Retain the explicit ten-entry rational slope parameter vector, the true tangent grid, the interval `0<epsilon≤10⁻⁵`, 32 triangles, and distinguished-line saturation. | Compatible seeds and doubling | A concrete compatible realization and uniform parameter certificate. The numerical 11:32 value and the Honma-based input already existed. |
| C10 | `families.tex`, `fam:doubling`; `BBLDoubling.doubling` | State the actual one-step theorem for `q=4r≥20`, the prescribed grid, simplicity, saturation, and positive central apex: `(q+1,T) → (2q+1,T+q²)`. Retain the mixed-triangle count and the preservation/replacement mechanism. | Compatible seeds and doubling | Full real-coordinate formalization of a specified BBL step. The doubling recurrence and its classical construction belong to Bartholdi–Blanc–Loisel, not to this project. |
| C11 | `families.tex`, `fam:eleven-family`, `fam:even-defect`, `fam:even-conditional`, `fam:recursive-quantifier`; `BBLSeed21`, `BBLNextSaturation`, `BBLGridReindex` | State the odd paper-supported family at `q=10·2^t`, the weaker even guarantee, and the stronger even target under its visibility invariant. Mention the verified 21-line parameter family and the exact remaining recursive transport/induction obligations. | Compatible seeds and doubling | Verified compatible seeds and substantial recursive interfaces. The full infinite iteration is not an end-to-end Lean theorem; the stronger even gain cannot be presented without its extra invariant. Published BBL iteration supplies the ordinary odd-family argument. |
| C12 | `upper_bounds.tex`, `upper:identity`, `upper:clean-charge`, `upper:fan-budget`; `FanGeometry`, `FanCount`, `CyclicFan`, `CleanLineBudget` | Retain elementary-segment accounting, the distinction between ordinary-ended and core-to-core shared sides, and the local fan restriction. Keep global incidence/charging hypotheses visible. | Multiplicities and restricted upper bounds | Local geometric and combinatorial formalization; multiplicity-sensitive accounting. The global extraction for arbitrary arrangements is not a completed Lean upper theorem. |
| C13 | `upper_bounds.tex`, `upper:weighted`, `upper:high-multiplicity`, `upper:two-core` | State the weighted inequality for even pairwise nonparallel arrangements and both restricted consequences: nonnegative core weight and at most two finite multiple points. Supply the short derivations and identify them as manuscript geometry. | Multiplicities and restricted upper bounds | Restricted nonsimple upper arguments. They do not lower the unrestricted classical upper envelope. Numerical first priority has not been established; Blanc's simple polynomial remains attributed to Blanc. |
| C14 | `upper_bounds.tex`, `upper:shared-fan`; `SharedFan` | Give the six equations for a triangle and its medians, six triangular cells, and six shared radial sides at the center. Explain the narrow consequence for the literal local reading of a cited shared-side statement. | Multiplicities and restricted upper bounds | Exact local geometric counterexample, fully formalized. It does not refute the final Clément–Bader upper theorem or an alternative endpoint-assignment argument. |
| C15 | `experiments.tex`, external local resolutions; exact source reports under `general-bounds/maiorana14` and `parpalak-utkin-current` | Preserve Maiorana's four local counts `52,52,53,52` from a 14:54 input and one sentence on the 132 gallery resolutions. State why triangle-nondecreasing smoothing and a universal loss-at-most-one rule fail. | Multiplicities or finite consequences, short paragraph | New diagnostic work on external constructions, with exact finite signs and counts. The input coordinates and their numerical records remain Maiorana's / the cited gallery's; the general small-perturbation interpretation is not fully formalized in Lean. |
| C16 | `formalization.tex`, frozen release and proof map | Give the pinned mathematical snapshot, ordinary-vs-native trust distinction, absence of active proof placeholders, and the repository/supplement link. State that 138 coordinate identities include 104 simple witnesses. | Verification and data availability | Reproducibility and trust-boundary audit. Declaration counts are implementation metadata, not counts of mathematical discoveries. |

## Compact selected finite-results table: ten rows maximum

Use the title **Selected exact witnesses and diagnostic inputs**, not “new
records”. Group orders by role rather than giving a truncated ranking. For
grouped lists, counts are paired with orders in the displayed order.

| Row | Orders or witness family | Counts / observation | Class and evidence | Reason to retain |
|---:|---|---|---|---|
| 1 | `28,30,34` | `238,275,357` | Simple; finite Lean certificates | Preserves all three historical Zarzuelo-attributed conclusions. Earlier numerical overlaps are acknowledged. |
| 2 | `39,51,99,195` | `470,818,3170,12482` | Simple; finite Lean and uniform theorem | All two-cap materializations; each is one above the preceding saved count, not asserted globally new. |
| 3 | `47,53,55,59` | `691,885,955,1103` | Simple; finite Lean and uniform theorem | One-cap materializations, including the search-to-proof motivating 47-line example. |
| 4 | `48,54,60` | `721,919,1141` | Simple; finite Lean and uniform theorem | Shifted even materializations. Rows 2–4 retain all eleven session gains without eleven separate table rows. |
| 5 | `44` | `608` | Simple; finite Lean lower certificate | Reaches Blanc's externally proved simple upper bound; does not prove classical optimality or numerical priority. |
| 6 | `11,21` | `32,132` | True-grid parameter families; formal statements and finite references | Compatible-seed contribution. Counts are inherited or below stronger known values; 21:133 remains known separately. |
| 7 | `q=80,160; n=q+1,q+2` | `(q²−4)/3` and `(q²−4)/3+q/2` | Simple; four finite Lean witnesses | Retains 81:2132, 82:2172, 161:8532, 162:8612 as sparse-family checkpoints, without pretending they close infinite iteration. |
| 8 | `321,322,641` | `34132,34292,136532` | Two independent exact counters; not promoted Lean certificates | Records the larger computational advance at the correct evidence level. Exclude 642:136852 from completed-result rows; mention its unfinished second count only in the supplement. |
| 9 | Maiorana `14:54` input | Local resolutions `52,52,53,52` | Nonsimple input; exact simple resolutions | Compact witness to the failure of nondecreasing smoothing; the input remains externally attributed. |
| 10 | Gallery inputs `8,20,26,32,38,50` | `15,117,204,315,450,792` | Nonsimple; imported exact finite certificates | Makes the simple/classical scope separation concrete. These are not new numerical discoveries of this project; the eight-line value has older priority. |

If ten rows plus grouped numeric lists are too wide, rows 2–4 can be replaced
by one row listing the eleven orders and stating “count = G(n), preceding saved
count + 1”. Nothing mathematical is lost because the formula is already
proved. Row 10 may instead become an attributed sentence. Conversely, do not
remove the evidence labels from row 8 just to save width.

Do not spend a separate row on reproduced optimal dyadic values such as
65:1365 and 129:5461. Their construction is established prior work; one cited
sentence can cover the corrected compatible five-line normalization and the
independent 19-line seed verification. The full catalog preserves every
coordinate identity and source attribution.

## Three figures with the highest explanatory value

1. **`../figures/affine-chart.pdf` — the main geometric mechanism.**
   It shows an exactly checked rational nine-line proxy changing from 18 to 20
   bounded triangular cells while retaining the old support triples. The
   caption must distinguish this finite illustration from the real all-order
   theorem and acknowledge the known 9:21 optimum. It should credit the
   underlying Füredi–Palásti family. The shifted phase gain and the six residue
   gains fit a short displayed formula or one-row table; they do not require
   separate figures in a 15-page article.
2. **`../figures/successor-49-resource.pdf` — why the original program needed a
   different construction.** The 49:767 chain and its collapsing exterior
   capacities explain a mathematical obstruction that a counts-only table
   hides. Keep “this chain” on the plotted capacities, and distinguish the
   general paper-level wedge-budget argument from the exact finite data. This
   plot must not be described as a counterexample to a recurrence for maxima.
3. **`../figures/shared-fan.pdf` — the nonsimple issue in one exact picture.**
   Six cells and six radial shared sides display why a local multiplicity
   argument needs careful endpoint accounting. Keep the explicit
   non-refutation of the final Clément–Bader theorem. This is more useful than a
   second quadratic-growth graph or a dense high-order arrangement image.

For the journal version, the figures may be reduced to a single full-width or
two-column-width panel each as layout permits; the sources are vector PDFs.
Do not imply that independent affine axis rescaling preserves angles or
lengths. No new or borrowed image is needed.

The discarded **plots**, not their mathematical content, remain in the
preserved long paper: growth and normalized gain are summarized by exact
formulas; residue gains by six integers; external smoothing by four counts;
family deficits by formulas and evidence labels; historical witnesses and seed
views by their exact equations/catalog links. The existing finite-envelope
plot displays classical saved counts and dated OEIS markers, not separate
simple and classical marker series; any reused caption must reflect that.

## What may move entirely to the long-paper supplement

- The 138-row identity catalog, full 3–60 table, and historical inventory, with
  a clear data reference in the short article.
- Three large historical arrangement figures and the two multiscale seed
  renderings; the short paper retains their counts, compatibility statements,
  and source references.
- Exhaustive module and declaration counts, build commands, hashes, and full
  axiom reports; keep the trust boundary and pinned release in the article.
- Individual million-proposal totals, elliptic/cubic search logs, fixed-seed
  SMT obstruction details, LP/MILP transfer attempts, and unfinished drafts.
  One paragraph may explain that these bounded searches produced no further
  verified improvement and are not impossibility proofs.
- Extended puzzle history, every literature-table discrepancy, and all OEIS
  attribution chronology. Keep citations establishing the baseline, BBL
  methods, simple upper bounds, stronger special families, and imported inputs.
- Conditional recurrence summation details and auxiliary arithmetic that are
  not new geometric results. Retain the unresolved recurrence and the distinct
  unconditional 49-seed numerical target.

## Page-budget guide

Aim for approximately 13.5–14 pages before final typography, leaving room for
reference growth. A possible budget, including figures where located, is:

| Component | Approximate pages |
|---|---:|
| Title, abstract, scope, definitions and cell interface | 1.5 |
| Uniform construction and affine-chart figure | 3.5 |
| Extension, quantitative gain, and resource figure | 1.7 |
| Compatible seeds, one-step doubling, family status | 2.0 |
| Multiplicity accounting, restricted consequences, shared-fan figure | 2.1 |
| Selected finite table, formal trust boundary, data and limitations | 1.4 |
| References | 1.3 |
| **Target total** | **13.5** |

This is an allocation, not a pretext to reduce font sizes or margins. If the
draft exceeds 15 pages, remove duplicated motivational prose, duplicate
finite tables, and search detail before cutting hypotheses, proof-status
qualifications, or attribution. Keep proofs of the main uniform theorem and
the distinct new restricted arguments coherent rather than scattering them
across unsupported theorem claims.

## Final coverage checklist

- [x] C1–C16 are represented at least by a precise statement, proof/interface,
  or explicit status paragraph in the short version.
- [x] The main construction remains affine, straight-line, simple, and valid
  for every natural order with the stated small cases.
- [x] Neither the all-parity maximal recurrence nor infinite Lean BBL
  iteration is accidentally stated as complete.
- [x] All restricted upper statements keep parity, nonparallelism, and core
  hypotheses; no simple upper theorem is transferred to classical K.
- [x] The ordinary defect/upper arguments are separated from their completed
  local Lean ingredients.
- [x] Imported counts and classical construction methods retain attribution.
- [x] Finite experiment failures and solver UNSAT results are not used as
  unrestricted upper theorems.
- [x] The short paper points to the full paper and machine-readable evidence;
  the original manuscript and results remain intact.
- [x] The compiled journal PDF is at most 15 pages including references.
