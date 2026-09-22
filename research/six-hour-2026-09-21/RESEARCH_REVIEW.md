# Kobon research: cumulative results, verification and next steps

**Research review prepared 22 September 2026, updated through 07:03 UTC.** The session was initially allocated six hours and then shortened to three hours, ending at 07:36:37 UTC. The directory retains its original name. This review covers the earlier repository work and the present session. The final build report records the complete release audit.

The strongest completed general result is an unconditional, explicit construction of simple real-line arrangements with

\[
G(n)=\begin{cases}
0,&0\le n<3,\\
1,&n=3,\\
\lfloor n(n-3)/3\rfloor+1+(n\bmod2),&n\ge4.
\end{cases}
\]

The theorem `Kobon.Universal.baseline_sound` proves this for **every natural number**, with no unproved geometric premise and no finite-testing assumption. It improves the previously formalized Füredi–Palásti lower formula at infinitely many orders. A separate verified envelope takes the maximum of this formula and all retained finite certificates. Neither theorem solves the Kobon problem, proves an arbitrary-seed successor recurrence, nor establishes numerical priority over all historical constructions.

## 1. Definitions and what “verified” means

Write `K(n)` for the classical maximum number of bounded triangular cells determined by n distinct real lines, allowing parallel lines and multiple intersections. Write `K_s(n)` for the maximum restricted to **simple** arrangements: no parallel pair and no triple concurrence. A simple construction proves a lower bound for both quantities. An upper theorem for simple arrangements need not bound the classical problem; current exact nonsimple examples demonstrate this distinction.

The repository now has three clearly separated levels of evidence:

* **General Lean theorems.** The geometry, the universal construction and the new local fan results use Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). They contain no `sorry`, custom construction axiom or native-evaluation dependency.
* **Finite Lean certificates.** Exact integer or rational coordinates are validated against geometric predicates. Some generated validations use `native_decide`, so their trust boundary includes Lean's native compiler/runtime. They are placeholder-free formal certificates, but that trust boundary is broader than the general kernel-only construction.
* **Independent exact computations and paper arguments.** These include two-counter checks of large or external witnesses, exact LP/SMT-related evidence, and general incidence arguments whose global encoding is unfinished. They are labelled as such and are not silently promoted to Lean theorems.

The geometric foundation has also become stronger. `Geometry.validate_sound` turns a successful coordinate certificate into actual real lines and nondegenerate empty triangles. `Simple.validate_simple_sound` proves simplicity when requested. The new `Cells` development proves that certified triangles have nonempty interiors, are strict sign cells of the arrangement and have pairwise disjoint interiors. This closes the earlier gap between the local triangle certificate and the usual cell interpretation of the Kobon problem.

## 2. The original extension program and its present status

The March 2026 materials remain in `archive/2026-03-original/` as provenance. Their original public Lean file contained eight placeholders, including the central `kobon_extension` step. They should not be presented as a completed proof of the general recurrence.

The finite inequalities 28:238, 30:275 and 34:357 associated with Alejandro Zarzuelo Urdiales are now supported independently by exact simple-arrangement certificates. OEIS explicitly attributes these entries to Zarzuelo and links the Archivara material. This establishes an attribution trail and reproducible finite lower bounds; it does not by itself establish the priority or truth of the stronger general recurrence.

The proposed all-parity recurrence

\[
K(n+1)\ge K(n)+\lfloor n/2\rfloor
\]

is **still unproved**. A counterexample to one proposed exterior-line choice refutes that particular construction rule, not the inequality for the maximum over all arrangements. The distinction matters: a successful all-n formula need not arise by adding one line to every preceding witness.

Several substantive parts of the extension program are now established:

* The Lean theorem `Exterior.extension` constructs an actual exterior line from a suitable visible-pair list, preserves the selected old triangles, keeps the arrangement simple, and produces the promised additional triangles. The unresolved part of a universal recurrence is the supply of sufficiently many visible pairs at every stage.
* A paper-level boundary-defect estimate, with `d=n(n-2)-3T`, gives an exterior gain at least `ceil((n-1) max(3,n-d)/(2n))` for the stated simple-arrangement hypotheses. The geometric visible-pair lower bound and its unused-edge charging proof are not yet fully formalized.
* The repository's repeated-exterior analysis shows why this method cannot simply deliver the full quadratic successor schedule forever. The boundary budget satisfies an inequality of the form `b_next + gain <= b + 2`. The exact chain starting from 49:767 gives 50:791, 51:814, 52:816 and 53:818, with available maximal exterior gains 24, 23, 2 and 2. This is a limitation of that method, not a disproof of a recurrence allowing reconstruction.

There is nevertheless an unconditional answer to the *numerical* target obtained by formally summing the conjectured recurrence from 49:767:

\[
K(n)\ge \left\lfloor\frac{(n-1)^2}{4}\right\rfloor+191
\qquad(n\ge49).
\]

`AllN.from_49_unconditional` and `Universal.dominates_49_target` establish this target using general constructions and finite base certificates. They do **not** assert that the 49-line configuration is extended one line at a time while preserving all its triangles.

## 3. The new universal construction

The underlying family is the classical Füredi–Palásti trigonometric arrangement. The first new formal component shifts its phase:

\[
\theta_i=\frac{(i+1/6)\pi}{n},\qquad
\sin\theta_i\,x+\cos\theta_i\,y=\sin(3\theta_i),
\quad 0\le i<n.
\]

The selected triples satisfy `i+j+k ≡ 0` or `n-1 (mod n)`. An exact determinant-sign proof establishes that these are actual uncut triangles. The modular count handles overlaps among repeated-index triples rather than discarding them unnecessarily, giving

\[
K_s(n)\ge\lfloor n(n-3)/3\rfloor+1\quad(n\ge3).
\]

The stronger final formula uses projective changes of affine chart. For odd n not divisible by three, exposing the unique rightmost vertex of a suitable half-phase arrangement produces one additional bounded triangle. For odd multiples of three at least nine, a chart just inside the two leftmost vertices retains two additional triangles. Lean verifies the exposed-cap inequalities, projective geometry, simplicity, retained triangles and counts. The relevant modules are `ShiftedCount`, `ShiftedFurediPalasti`, `FurediPalastiCaps`, `FurediPalastiTwoCaps` and `Universal`.

Against the previously formalized all-n baseline

\[
B(n)=\lceil n(n-3)/3\rceil,
\]

the exact improvement for n at least four is:

| n modulo 6 | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| G(n)-B(n) | 1 | 1 | 0 | 2 | 0 | 1 |

Thus every odd order at least five improves, as does every positive multiple of six. The leading term remains `n²/3-n`: this is a constant-term improvement on four residue classes, not a new asymptotic density. Its exact arithmetic distance from `floor(n(n-2)/3)` is

`floor(n/3) + 1[n mod 3=2] - 1 - (n mod 2)`.

The theorem stating this identity does not assume or prove that the comparison polynomial is an upper bound in every variant of the problem.

The universal envelope is `Universal.bound n = max (G(n)) (AllN.bound n)`. It keeps all stronger saved finite constructions while remaining defined and proved for every natural number. It should be the default answer when asking for the strongest **verified all-order lower-bound function retained by this project**.

## 4. Finite improvements and external records

The following simple finite witnesses were promoted and compiled during this session. The comparisons are with this repository's preceding retained values, not a claim that each new value is a first publication or beats every construction in the literature.

| Lines | Previous retained value | New verified value |
|---:|---:|---:|
| 39 | 469 | 470 |
| 47 | 690 | 691 |
| 48 | 720 | 721 |
| 51 | 817 | 818 |
| 53 | 884 | 885 |
| 54 | 918 | 919 |
| 55 | 954 | 955 |
| 59 | 1102 | 1103 |
| 60 | 1140 | 1141 |
| 99 | 3169 | 3170 |
| 195 | 12481 | 12482 |

These gains arise from the phase/chart work. The older values 39:469, 51:817, 99:3169 and 195:12481 had also been obtained from another construction; the shifted classical family already gives them, and the final odd-order formula exceeds them by one. They are therefore not numerically distinctive of the earlier additional-line family.

The retained simple construction 44:608 remains useful: it meets Blanc's simple upper bound at that order. This alone does not establish optimality in the unrestricted classical problem.

The current source audit also found stronger **external** finite witnesses missing from the repository's older coordinate catalog. Both independent exact counters agreed on the complete triangle sets for the Parpalak–Utkin gallery's 8:15, 14:54, 20:117, 26:204, 32:315, 36:402, 38:450, 42:553, 46:667 and 50:792 arrangements. The current OEIS page already lists these values; they should not be presented as missing OEIS records. The eight-line result has older discovery priority; the gallery is our coordinate source.

All fifteen of Andrea Maiorana's published 14:54 certificates were also independently checked. Fourteen have exactly two triple points and one has four. The exact source files, CC-BY 4.0 licence and commit attribution are retained. These constructions remain attributed to their authors. Their Lean promotion is tracked by the final certificate catalog and build report, separately from the completed independent computations.

Source snapshots are immutable: Maiorana commit `e47c7cfd9661e54d29befb83118bf83d5f804028` and Parpalak–Utkin gallery commit `feae4f5571a988a3ed45bd26a36259ebb7d7d3d2`. See the two `INDEPENDENT-REVIEW.md` files under `general-bounds/maiorana14/` and `general-bounds/parpalak-utkin-current/`.

## 5. Hybrid constructions and the remaining infinite-iteration theorem

The project has a concrete tangent-grid-compatible realization of the known 11:32 value. `SeedFamily` proves the true trigonometric construction throughout `0<epsilon<=10^-5`, including all 32 triangles and nine caps along the distinguished line. This is a geometric family theorem, not just a floating-point fit.

The associated BBL-style manuscript family uses

\[
q=10\cdot2^t,\qquad n=q+1,\qquad
T=\frac{q^2-4}{3}.
\]

The finite values 11:32, 21:132, 41:532, 81:2132 and 161:8532 have exact witnesses. The 21- and 41-line values are below the known 133 and 533. A sharper boundary-invariant argument also gives the proposed even companion

\[
K_s(q+2)\ge\frac{q^2-4}{3}+\frac q2,
\]

with checked examples 12:37, 22:142, 42:552, 82:2172 and 162:8612. The small members do not replace stronger existing records. New large rational witnesses 321:34132, 322:34292 and 641:136532 passed two independent exact counters during this session; the largest coefficients have more than 1100 digits and these have not been promoted to Lean finite certificates at this snapshot. A 642:136852 coordinate file passed adjacency and simplicity checks, but its second independent count was interrupted when the session was shortened; that last candidate remains incomplete evidence.

Formalization of the general doubling step advanced substantially. The completed components include:

* Exact integer crossing profiles and the `q²` mixed-triangle count (`BBLCount`, `BBLRowGeometry`).
* Cap uniqueness, uncut cap sides, endpoint-sign envelopes, central retained-triangle signs, and the combinatorial bookkeeping for retained and new triangles (`BBLCaps`, `BBLCapSigns`, `BBLCapEnvelope`, `BBLCapHeight`, `BBLCentralEnvelope`, `BBLLiftedKeys`, `BBLLiftedRows`, `BBLConsecutive`, `BBLRowMax`, `BBLAssembly`).
* Actual trigonometric pencil profiles for every `q=4r`, `r>=5`, and every `epsilon` in `(0,tan(pi/(2q)))`, valid for sufficiently small positive `delta` (`BBLPencilProfiles.pair_profile_eventually`).
* Simultaneous profile regularity, avoidance of parallel directions and the bridge from analytic coordinates to the crossing expressions (`BBLPencilRegularity`, `BBLCrossingCoordinates`).
* The full actual `CrossingOrder`, including the distinguished line, and injectivity along every new row for sufficiently small nonzero `kappa` (`BBLRealization`, completed at 06:42 UTC).
* An actual simple real arrangement with at least `q²` mixed triangles (`BBLRealizedPencil.realized_pencil_exists`, completed at 06:47 UTC): for each `q=4r>=20` and prescribed old tangent grid with `0<epsilon<tan(pi/(2q))`, any simple graph-line arrangement on that grid admits positive `delta` and `kappa` producing the claimed arrangement of `2q+1` lines.
* The canonical endpoint-product bridge to the actual cap-persistence and reindexing theorem (`BBLCapBridge`, completed by 06:50 UTC).

The actual one-step geometric theorem is now complete. `BBLDoubling.doubling` proves that, for every q=4r at least 20 and 0<epsilon<tan(pi/(2q)), a simple seed on the prescribed tangent grid with all distinguished-line segments triangular and its central apex above that line produces 2q+1 lines and at least T+q² triangles. The proof derives crossing order, injectively preserves the old triangle count through surviving and replacement triangles, and supplies q² disjoint mixed triangles. It compiled with only standard logical axioms. The accompanying visible-list assembly proves a gain of at least q/2 once its geometric visibility hypotheses are supplied.

The theorem is not yet an end-to-end infinite iteration. Witness transport through the sorting permutation, the finite 21-line seed's exact label conversion, induction with explicit parameter quantifiers, and the full quantitative exterior invariant remain additional obligations. The new `BBLGridReindex` proves the doubling-grid permutation and its trigonometric identity. `BBLNextSaturation.next_saturated` also proves that every consecutive next-grid pair supports an actual triangle with the distinguished line, in canonical labels; it passed at 07:03 UTC. These complete further parts of the recursive seed-shape argument.

The construction does not apply to an arbitrary optimal arrangement merely because it has a saturated line. Its prescribed tangent-grid intercepts impose cross-ratio constraints. Moreover, a single fixed positive `epsilon` is not asserted to work for infinitely many iterations: the manuscript chooses an adequately small parameter for each finite depth, for example `min(10^-5,1/(40·2^t))`.

A published Parpalak–Utkin 19-line seed was independently checked over `0<epsilon<=1/1000`: 1632 exact endpoint determinant checks, 107 triangles, and all seventeen distinguished-line caps. This reproduces part of their `18·2^t+1` construction; its mathematical attribution remains theirs.

## 6. New upper-bound structure: multiplicities and local fans

The upper-bound work begins with exact segment accounting rather than applying a simple-arrangement theorem to a nonsimple configuration. Let `P` count parallel pairs, let `t_r` count finite r-fold points, let `S=sum r(r-2)t_r`, and let `E`, `U`, `D` count bounded elementary segments, unused segments and segments shared by two triangular cells. When every line meets another line,

\[
E=n(n-2)-2P-S,\qquad 3T=E-U+D,
\]

so the defect satisfies

\[
\delta=n(n-2)-3T=2P+S+U-D.
\]

The ledger includes the correction needed when some lines are isolated. These identities expose precisely what a multiplicity-sensitive upper proof must control.

For **even n at least four with no parallel pair**, a paper-level clean-line charging argument and a geometric fan bound give

\[
2\delta\ge n+\sum_{r\ge3}(2r^2-11r+6)t_r.
\]

The coefficients at r=3,4,5,6 are respectively -9,-6,1,12. Thus triple and quadruple points are the obstruction in this accounting scheme. If all multiple points have multiplicity at least five, or the displayed weighted sum is nonnegative, the same polynomial bound as Blanc's even simple theorem follows:

\[
T\le\left\lfloor\frac{n(n-5/2)}3\right\rfloor.
\]

A sharper fan analysis for at most two finite multiple points, of any multiplicity, yields

\[
T\le\left\lfloor\frac{n(n-5/2)}3\right\rfloor+1.
\]

These are restricted paper-level upper results with unestablished numerical priority. They are not an unrestricted classical upper theorem. The no-parallel hypothesis is essential to the current proof: three parallel vertical lines and one horizontal line already invalidate the proposed clean-line local argument if that hypothesis is removed.

Five new Lean modules prove the main local geometric and arithmetic ingredients:

| Module | Completed result |
|---|---|
| `FanGeometry` | Actual triangle-support propagation through ordinary endpoints; a fan strip cannot connect opposite rays. |
| `FanCount` | The cyclic count turning the no-long-run property into at most `2r-3` selected ordinary shared rays. |
| `CyclicFan` | Actual antipodal ray and sector geometry implies that no-long-run property. |
| `CleanLineBudget` | Nine arithmetic consequences with all still-needed incidence and charging hypotheses explicit. |
| `SharedFan` | Six actual empty triangles around a triple point have six distinct elementary radial sides, each shared by two triangles. |

All five compiled with standard axioms only. The global extraction of cyclic sectors from arbitrary arrangements and the clean-line charging argument remain to be encoded. An exact audit passed 597 retained/random/two-pencil cases and then 25 current external witnesses; these finite checks supplement rather than replace the general argument.

`SharedFan` also cautions against a literal local reading of a phrase in the Clément–Bader draft about incident triangle pairs. It does not refute the draft's final theorem: an intended assignment of shared edges to endpoints would be a different statement. The source audit preserves that distinction and treats the classical envelope as a reported external result whose local proof wording requires clarification.

## 7. What failed, and why those failures are useful

Several natural shortcuts are now ruled out for explicit configurations. Most strikingly, smoothing multiple points need not preserve the triangle count. All four local simple resolutions of Maiorana's two-triple 14:54 example have 52, 52, 53 and 52 triangles. The obstruction occurs even before any concern about global realizability of resolution signs. For the gallery's collinear-core examples, all 132 local resolutions were realized by independent exact private-line offsets and checked by both counters. The best nearby simple counts at n=8,14,20,26,32,38,50 are 14,51,114,203,313,448,791. A universal nondecreasing smoothing theorem and a universal collinear-core loss-at-most-one rule are therefore both false.

Other searches constrain the next research choices without proving impossibility:

| Direction | Recorded outcome and scope |
|---|---|
| Nonuniform nodal-cubic angles and Fourier deformation | Millions of proposals; no retained improvement. A 39-line Fourier run tested 2,687,600 proposals. |
| Real elliptic torsion groups | Some larger projective triangle counts, but affine charts lost too many faces; no improvement over retained affine bounds. |
| Exact fixed-configuration chart tests | SMT obstructions show, for example, that the saved 48-line cubic seed with 724 projective triangles cannot retain 722 in any affine chart. These are solver results for fixed exact seeds, not universal theorems or Lean proofs. |
| Projective triangle mutations | The final 39-line beam examined 2,122,270 candidate edges through 4559 states without exceeding 470 affine / 471 projective triangles even combinatorially. The 48-line LP run accepted 471 mutations and retained 721 / 724. |
| Kinetic chamber rays | No improvement in 21,488,140 offset chambers at n=39, or 9,712,359 / 24,634,918 / 24,427,315 joint chambers at n=39 / 40 / 48. Numerically unsuccessful rays were discarded; these are bounded search results, not upper theorems. |
| Singular-boundary search at 44 lines | Single collapses and 35,352 paired collapses did not beat 608. The saved beam checkpoint has 771 states and 446,422 candidate edges with no improvement; an unfinished round was discarded. |
| Partial BBL deletion | Tested greedy/structured subsets did not improve the universal formula. This was not exhaustive over all subsets or all base types. |
| Tangent-grid LP/MILP transfer | The tested optimal 23-line projective charts had no positive-margin transfer; a constrained near-optimal search produced 144 with the required caps, below an already known compatible 145. These are bounded searches, not global nonexistence proofs. |
| Turning FP infinity into the distinguished BBL line | The direction grid matches, but the tested arrangements have too few distinguished-line caps. Grid compatibility alone is insufficient. |

The earlier project also recorded 1,274,096 vertex-chord insertion tests and 5,867,928 local one-line proposals without improving their selected seeds. Scripts, parameters, source snapshots, checkpoint files and exactness boundaries are listed in the workstream experiment registers. Future work should begin there instead of repeating the same local neighborhoods.

## 8. Attribution and the defensible novelty claim

An all-n lower formula already exists in the literature. Füredi and Palásti's 1984 construction gives the classical baseline; later primary sources explicitly state it. Their original projective count table contains constant terms related to the present refinement. We have not located an explicit prior statement of the exact affine function `G`, but this is not enough to establish its first numerical priority.

A defensible description of this project's completed contribution is:

> We give a complete Lean formalization of an explicit parity-sensitive affine refinement of the Füredi–Palásti construction, producing simple arrangements with at least `floor(n(n-3)/3)+1+(n mod 2)` triangular cells for every `n>=4`. We combine it with a verified finite-certificate envelope, independently reproduce current external constructions with exact coordinates and attribution, and develop new formal geometric components for extension, doubling and multiplicity-sensitive upper-bound arguments. Numerical first priority for the affine refinement and a fully formal infinite doubling iteration remain separate unresolved questions.

The original finite Zarzuelo attributions should be retained, together with the archived March claim and the current proof status. The later rigorous results supersede the need to rely on the March file for those finite bounds, but they do not retrospectively prove its unqualified recurrence.

No public Kobon proof was supplied by the reported OpenAI rumor. The official mathematics advisory announcement discusses a collection of internal results without identifying Kobon. The public ProofAtlas discussion still treats the Kobon problem as open. This research does not claim to replicate an unpublished solution.

## 9. Priority for the next session

1. Finish the BBL seed reindexing and recursive-shape integration; actual crossing order and one-step cap retention are now proved. Preserve the exact distinction between a `q²` mixed-triangle theorem, a `T+q²` one-step theorem, and a repeatable infinite-family theorem.
2. Complete the global arrangement-to-fan extraction and clean-line charging formalization. The local geometric core is now available in Lean.
3. Seek a sharper parity budget for many triple and quadruple points. Higher multiplicities already have favorable weight; the current obstacle is the low-multiplicity core and how shared edges interact globally.
4. Search singular arrangements and different projective topologies, rather than relying exclusively on smoothing or local chart changes. The exact counterexamples and chart obstructions justify this change of emphasis.
5. Audit affine refinements of Füredi–Palásti in the primary literature before claiming numerical first priority. The complete formal construction is already a meaningful deliverable independent of that historical question.
6. Reuse the current external certificates and immutable source snapshots when updating lower-bound tables. Separate our new constructions, our independent verification of others' constructions, reported external upper bounds and fully checked theorems.

## 10. Primary sources and evidence map

* Füredi and Palásti, *Arrangements of lines with a large number of triangles* (1984), [DOI](https://doi.org/10.1090/S0002-9939-1984-0760946-2). See `general-bounds/lower-bound-priority-audit.md` for the original projective table and affine-priority discussion.
* Felsner and Kriegel, *Triangles in Euclidean Arrangements* (1999), [author-hosted paper](https://page.math.tu-berlin.de/~felsner/Paper/tri.pdf); Erickson's [convex-hull paper, §7.2](https://jeffe.cs.illinois.edu/pubs/pdf/convex.pdf) also states the general FP lower bound.
* Nicolas Bartholdi, Jérémy Blanc and Sébastien Loisel, *On simple arrangements of lines and pseudo-lines in P² and R² with the maximum number of triangles*, [primary preprint](https://arxiv.org/html/0706.0723v1).
* Jérémy Blanc, [2008 primary preprint](https://arxiv.org/html/0801.2845v2). Its stronger even upper bound concerns simple arrangements.
* Clément–Bader, [2007 draft](https://oeis.org/A006066/a006066.pdf). See `general-bounds/upper-bound-scope-audit.md` and `upper-scope-table.md` for precise scope and the local proof-wording issue.
* [OEIS A006066](https://oeis.org/A006066), the principal community index and attribution ledger; it is not a substitute for checking the hypotheses of cited upper theorems.
* Savchuk, [2025 preprint](https://arxiv.org/abs/2507.07951); Parpalak–Utkin, [2026 preprint](https://arxiv.org/html/2604.22035v1) and [coordinate gallery](https://github.com/ud1/kobon-solutions).
* Andrea Maiorana, [14-line exact certificate repository](https://github.com/rufio72/kobon_triangles_k14), with licence and immutable provenance retained locally.
* [ProofAtlas Kobon discussion](https://www.proofatlas.ai/collaboration/kobon-triangle-problem/) and the [official OpenAI mathematics advisory announcement](https://openai.com/index/advisory-group-on-mathematics-and-ai/).
* The earlier claimed exact 22/28 values in one Zenodo preprint were superseded by its [version 4](https://zenodo.org/records/21181834), which gives symmetry-restricted conclusions. Earlier stronger claims are not used as established exact values here.

Start a resumed investigation with this review, `RESEARCH_LEDGER.md`, `FORMALIZATION.md`, `RESULTS.md`, `phase-proof.md`, the three workstream READMEs, and their experiment registers. The final release/build manifest supplies the last-minute compilation and certificate-promotion status.
