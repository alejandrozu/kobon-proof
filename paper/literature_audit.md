# Literature and upper-bound authoring audit

Prepared 22 September 2026 for the sole-author manuscript by Alejandro Zarzuelo Urdiales. This file records the source basis and limitations of `sections/literature.tex`, `sections/upper_bounds.tex`, and `references.bib`. It is not an exhaustive priority clearance or a substitute for the cited proofs.

## Bibliographic verification

The bibliography contains 29 references. Journal metadata were checked against exact Crossref DOI records, author publication pages, publisher pages, or primary manuscripts. Preprint and publication dates are deliberately distinguished. GitHub data sources are pinned to immutable commits. Descriptive repository titles are not represented as published article titles.

| Key | Verified metadata / primary source | Use and limit |
|---|---|---|
| `fujimura1978` | Fujimura, *The Tokyo Puzzles*, Scribner, New York, 1978; Gardner editor, Fumie Adachi translator; ISBN0684155362. [NII catalogue](https://cir.nii.ac.jp/crid/1971712334767785501), linked Library of Congress record77026661. | Puzzle history; not a newly inspected original proof of Tamura's upper polynomial. |
| `gardner1983` | *Wheels, Life, and Other Mathematical Amusements*, W.H.Freeman, New York,1983; relevant pages170–171,178 identified by Clément–Bader. | Historical discussion; page attribution is explicitly through the checked CB draft. |
| `grunbaum1972` | *Arrangements and Spreads*, CBMS10, AMS,1972; DOI[10.1090/cbms/010](https://doi.org/10.1090/cbms/010), verified in AMS bibliography and book metadata. | Arrangement framework. Complete book chapters were not read in this audit; no uninspected theorem is used as a new premise. |
| `strommer1977` | Thomas O.Strommer, JCTA23(3),314–320; DOI[10.1016/0097-3165(77)90022-X](https://doi.org/10.1016/0097-3165(77)90022-X); Crossref exact record. | Early extremal-triangle literature; no unverified affine/classical formula attributed. |
| `purdy1979` | G.B.Purdy, Discrete Math25(2),157–163; DOI[10.1016/0012-365X(79)90018-9](https://doi.org/10.1016/0012-365X(79)90018-9); Crossref. | Historical context only; full publisher text was inaccessible. |
| `purdy1980` | George Purdy, Proc.AMS79(1),77–81; DOI[10.1090/S0002-9939-1980-0560588-4](https://doi.org/10.1090/S0002-9939-1980-0560588-4); Crossref. | Historical context, not an uninspected classical upper theorem. |
| `furedipalasti1984` | Zoltán Füredi and Ilona Palásti, Proc.AMS92(4),561–566; AMS DOI[10.1090/S0002-9939-1984-0760946-2](https://doi.org/10.1090/S0002-9939-1984-0760946-2). Alternative JSTOR DOI10.2307/2045427 identifies the same paper. [Primary text mirror](https://paperzz.com/doc/9476977/arrangements-of-lines-with-a-large-number-of-triangles). | Trigonometric construction and projective Table1. Chart boundedness is a separate obligation. Publisher endpoint returned403; mirror and DOI records checked. |
| `harborth1985` | Ann.NYAcad.Sci440(1),31–33; [Wiley primary DOI page](https://nyaspubs.onlinelibrary.wiley.com/doi/10.1111/j.1749-6632.1985.tb14536.x). | Pseudoline history; no assumption of stretchability. |
| `roudneff1996` | JCTB66(1),44–74; DOI[10.1006/jctb.1996.0006](https://doi.org/10.1006/jctb.1996.0006); Crossref. | Pseudoline extremal context; numerical facts not copied from uninspected full text. |
| `forge1998` | David Forge,Jorge Luis Ramírez Alfonsín, DCG20(2),155–161; DOI[10.1007/PL00009373](https://doi.org/10.1007/PL00009373); Crossref. | Scope explicitly confirmed by BBL's primary introduction: projective2·2^t+2 and affine2·2^t+1. |
| `felsnerkriegel1999` | Stefan Felsner,Klaus Kriegel, DCG22(3),429–438; DOI[10.1007/PL00009471](https://doi.org/10.1007/PL00009471); [author PDF](https://page.math.tu-berlin.de/~felsner/Paper/tri.pdf). | Euclidean baseline and straight/pseudoline distinction. |
| `erickson1999` | Jeff Erickson, SIAMJComput28(4),1198–1214; DOI[10.1137/S0097539797315410](https://doi.org/10.1137/S0097539797315410); Crossref and [author manuscript](https://jeffe.cs.illinois.edu/pubs/pdf/convex.pdf). | Section7.2 states the ceiling baseline. Its three-angle modification is for a decision-tree argument, not a universal successor construction. |
| `clementbader2007` | **Gilles Clément and Johannes Bader**, *Tighter Upper Bound for the Number of Kobon Triangles*, draft21Dec2007; [OEIS-hosted primary PDF](https://oeis.org/A006066/a006066.pdf). | Source-reported classical envelope; no DOI invented and no original Tamura publication located. Local wording separately audited. |
| `bbl2008` | **Nicolas Bartholdi,Jérémy Blanc,Sébastien Loisel**; Contemp.Math453(2008),105–116, *Surveys on Discrete and Computational Geometry*; DOI[10.1090/conm/453/08797](https://doi.org/10.1090/conm/453/08797). [arXiv0706.0723v1](https://arxiv.org/html/0706.0723v1),5Jun2007. | Simplicity restrictions, tangent-grid doubling, straight/pseudoline family distinction. Bader and Bartholdi must not be confused. |
| `blanc2011` | Jérémy Blanc, Geombinatorics21(1)(2011),**5–14**; arXiv0801.2845 first posted2008. [Author list](https://algebra.dmi.unibas.ch/blanc/publications.html), [author PDF](https://algebra.dmi.unibas.ch/blanc/articles/bestbound.pdf), [arXiv](https://arxiv.org/abs/0801.2845). | Simple affine even upper polynomial. No journal DOI found. Proposition numbering varies by version, so text refers to Section2. |
| `damasdi2020` | Gábor Damásdi,Leonardo Martínez-Sandoval,Dániel T.Nagy,Zoltán Lóránt Nagy; Discrete Math343,112105; DOI[10.1016/j.disc.2020.112105](https://doi.org/10.1016/j.disc.2020.112105); [primary PDF](https://real.mtak.hu/114794/7/1-s2.0-S0012365X20302910-main.pdf). | Section3 summary; area constraints are a different extremal objective. |
| `savchuk2025` | Pavlo Savchuk, [arXiv2507.07951v1](https://arxiv.org/html/2507.07951v1). | 23/27 straight constructions, reported11-line exclusion, Honma-based11 seed AppendixA.4; SAT upper run not replayed. |
| `parpalakutkin2026` | Roman Parpalak,Denis Utkin, [arXiv2604.22035v1](https://arxiv.org/html/2604.22035v1),23Apr2026. | Theorem5.1 straight18·2^t+1 family. Coordinate checks do not reproduce every external proof. |
| `parpalakutkinEven2026` | [Pinned draft](https://github.com/parpalak/kobon-even-draft/blob/4da100acd30d9fb2c5b2a1fa3fb9ce848a2e52a5/8-14-26-even-series.md), commit4da100acd30d9fb2c5b2a1fa3fb9ce848a2e52a5. Descriptive English title. | Russian text states nonsimple6·2^t+2 family, two triple points, count(n(n−5/2)+1)/3. Full proof not formalized here. |
| `parpalakutkinGallery2026` | [Gallery snapshot](https://github.com/ud1/kobon-solutions/tree/feae4f5571a988a3ed45bd26a36259ebb7d7d3d2),21Sep2026. | Ten coordinate witnesses independently counted. Earlier8-line credit retained. No LICENSE/COPYING/NOTICE found in the inspected tree; no license grant asserted. |
| `maiorana2026` | Andrea Maiorana, [snapshot](https://github.com/rufio72/kobon_triangles_k14/tree/e47c7cfd9661e54d29befb83118bf83d5f804028),12Aug2026. | Fifteen14:54 witnesses. Original CC BY4.0 license and attribution retained. Source's global-optimality assertion not imported. |
| `liangliuZhang2026` | Ke Liang,Youming Liu,Yurui Zhang, *On the symmetries of optimal simple Kobon arrangements for n=28*, version4,3Jul2026; DOI[10.5281/zenodo.21181834](https://zenodo.org/records/21181834). | Version4 concerns symmetry, not an unrestricted exact value. Its stated upper239 for the simple problem is not adopted instead of Blanc's238. |
| `oeisA006066` | [A006066](https://oeis.org/A006066), consulted22Sep2026; revision245 dated14Sep2026 inspected. | Index of values and credits, not exhaustive priority proof or blanket justification of every upper bound. |
| `zarzuelo2026` | [Archivara March paper](https://archivara.org/paper/48b411c9-0e03-4592-931e-179b9a1c2312). | Archived Lean had eight placeholders including the general extension. Finite28/30/34 claims now separately certified. |
| `zarzueloRepository` | [Actual git origin](https://github.com/alejandrozu/kobon-proof), confirmed by `git remote -v`. | Reproducible research and theorem inventory. Descriptive repository title. |
| `handwiki2026` | [Kobon page](https://handwiki.org/wiki/Kobon_triangle_problem),22Sep2026. | Record of the attributed recurrence; a secondary page does not prove it. |
| `proofatlas2026` | [Research page](https://www.proofatlas.ai/collaboration/kobon-triangle-problem/),22Sep2026. | Reported restricted14-line upper and open status; underlying proof/programs not replayed. |
| `lean4` | Leonardo de Moura,Sebastian Ullrich, CADE28(2021),625–635; DOI[10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37); Crossref. | Proof-system infrastructure. |
| `mathlib` | The mathlib Community, CPP2020,367–381; DOI[10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824); [primary PDF](https://leanprover-community.github.io/papers/mathlib-paper.pdf). | Library infrastructure. |

Exact DOI requests succeeded for the listed journal metadata. A later rapid Crossref bibliographic-query batch was rate-limited (429); stale loop output after failures was discarded. Blanc's page range was recovered from the author's own list. In particular, `10.1137/S0097539795284420` is **not** the verified Erickson DOI and is not used.

## Priority and numerical comparison decisions

1. An all-n construction predates this project: B(n)=ceil(n(n−3)/3). Claims of the first general lower bound are excluded.
2. For n≥4, G−B by n mod6 is [1,1,0,2,0,1]. This is a constant-term improvement; the n² and n coefficients do not improve.
3. Original FP projective P satisfies P−G=[−1,0,2,1,2,0] for n≥5. Projective faces require an affine-chart argument; they are neither ignored nor automatically counted as bounded affine faces.
4. Numerical first priority for G has not been established. The safe principal contribution is the complete geometric Lean formalization of the explicit affine refinement, including chart boundedness.
5. G is not strongest at every order. Published special families and the repository's finite maximum improve it. A maximum with sparse families, extended by padding, is itself an all-n function.
6. Parpalak–Utkin's straight18·2^t+1 count exceeds G there by6·2^t−2. BBL's original18-series was pseudoline; its straight6/14-series and Forge's2-series are distinct.
7. BBL2007 explicitly prints30:275 in bold, identified by its legend as straight realizable. Its28:238 entry is not bold and does not alone establish straight realization. Savchuk later describes the27→28 extension.
8. The older perfect33-line construction belongs to Forge–Ramírez Alfonsín's2·2^t+1 family (equivalently q=4·2^t with shifted parameter). Neither BBL's6-series nor14-series contains33. The34:357 consequence is not first numerical priority for this project. The internal module name `TamuraSeed5` does not independently establish historical attribution to Tamura for that family.
9. The March successor claim remains unproved. Later independent all-n constructions, finite extensions, or visibility-hypothesis theorems do not prove it retroactively.
10. BBL's T+q² step is published prior work. Our q=4r≥20 specialization is completed real geometry. End-to-end recursive Lean iteration remains open despite completed reindex and next-saturation components.

## Upper-section proof audit and boundaries

The section follows `general-bounds/clean-line-parity.md`, `multiplicity-budget.md`, and `upper-bound-scope-audit.md`, and reads the actual completed modules rather than extrapolating from prose summaries.

- The general segment identity retains isolated lines: a counts lines with finite intersections, E=n(n−1)−2P−S−a, and δ=2P+S+a−n+U−D. The simplification a=n is conditional.
- All clean-line charging and derived upper theorems assume **even n≥4 and pairwise nonparallel lines**. Three parallel verticals plus one horizontal defeat the attempted weaker local hypothesis. Conditional arithmetic with P does not prove geometric charging with parallels.
- The clean-line proof is expanded as an induction, including the first/last transverse-line intersection. No unexplained “word for word” generalization remains.
- `FanGeometry` proves ordinary-endpoint support propagation and the opposite-ray obstruction for real geometry. `CyclicFan` proves the geometric no-long-run bridge. `FanCount` proves cyclic counting. Extraction from an arbitrary global arrangement is still required.
- `CleanLineBudget` proves nine arithmetic implications with explicit geometric-budget hypotheses. It is not an unconditional upper theorem for K.
- The manuscript-weighted result is2δ≥n+Σ(2r²−11r+6)t_r. Negative triple/quadruple weights prevent applying the simple polynomial to arbitrary classical arrangements.
- The at-most-two-core-point result is an ordinary geometric theorem with upper floor(n(n−5/2)/3)+1. The special d2≤1 sector argument and global extraction are not fully Lean encoded.
- At8,14,26,50 that restricted bound is attained by attributed exact no-parallel/two-triple witnesses15,54,204,792. This is restricted sharpness, not unrestricted optimality or numerical priority.
- `SharedFan` checks six actual empty triangles, disjoint nonempty interiors, six distinct nonzero elementary radial sides, and their sharing. It refutes a literal local incidence interpretation of one CB sentence, **not the final Clément–Bader theorem**. The new vector figure uses its exact six-line equations.
- The four local resolutions of a selected Maiorana14:54 witness were exact-counted as52,52,53,52. Identifying all sufficiently small perturbations additionally uses the manuscript determinant-sign/continuity argument; it is not a Lean classification theorem.
- The597-arrangement check corroborates the accounting experimentally; it is not a general proof. Later imported witness checks are separately recorded.

Completed local modules are `SharedFan`, `CleanLineBudget`, `FanGeometry`, `FanCount`, `CyclicFan`. Saved build/axiom outputs are `research/six-hour-2026-09-21/general-bounds/lean-build.log` and `lean-axioms.log`. No Lean source or compiler was changed/run while authoring these sections.

## Editorial and integration notes

- Sole manuscript author remains Alejandro Zarzuelo Urdiales; cited constructions retain original attribution.
- The upper section includes `figures/shared-fan.pdf` with label `fig:shared-fan`. No external artwork was copied.
- Full BBL authorship, Blanc's2011 publication date, and Forge's33-line source were checked against primary metadata.
- All29 bibliography entries are cited in the literature section. Other sections reuse the agreed keys. No rumor of a solved Kobon problem is mathematical evidence here.
- A first-numerical-priority claim requires broader historical work, including the relevant full chapters of Grünbaum, affine-chart follow-ups, and unpublished construction notes. The formalization claim does not depend on completing that search.

## Rendered-page review

The complete rendered pages51–60 were visually inspected individually at105dpi. Bibliography names, accents, formulas, long links, and all29 entries were legible. The138-certificate catalogue, historical table, and final evidence-path table had no clipped contents. One defect was reported to the integrating author: on page55, Table10's four-digit G and saved-simple entries at orders57–60 touched visually because the numeric columns were too close. The integrating author owns the spacing correction and final rerender. The bibliography ends on a deliberately short page before the appendix; this is an explicit section break rather than missing text.
