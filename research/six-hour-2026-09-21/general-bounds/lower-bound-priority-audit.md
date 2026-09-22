# Priority audit of the all-n affine lower bound

Audit date: 2026-09-22. This is a source review, not proof that no unlocated publication contains an equivalent refinement.

## What can safely be claimed

An all-n quadratic lower construction already existed in the literature. The classical baseline is

`B(n) = ceil(n(n-3)/3)`.

The present work constructs and formally verifies an affine refinement

`G(3)=1; G(n)=floor(n(n-3)/3)+1+(n mod 2)` for `n>=4`.

Thus `G-B` is 1 for `n=0,1,5 (mod 6)`, 2 for `n=3 (mod 6)`, and 0 for `n=2,4 (mod 6)`. Finite certified seeds and separately verified extension families can exceed G at individual orders. G is a uniform guarantee, not a claim to match all individual records.

The strongest presently justified novelty description is: **a self-contained Lean formalization of an explicit all-n affine refinement of the Füredi–Palásti family, including the projective chart argument needed to retain the additional bounded triangles.** The improvement over the standard quoted baseline is proved. First publication of the numerical formula has not been established by this audit.

## Primary-source comparison

### Füredi and Palásti, 1984

[Arrangements of lines with a large number of triangles](https://paperzz.com/doc/9476977/arrangements-of-lines-with-a-large-number-of-triangles), Proceedings AMS 92(4), 561–566, DOI 10.2307/2045427.

The AMS publisher DOI is also [10.1090/S0002-9939-1984-0760946-2](https://doi.org/10.1090/S0002-9939-1984-0760946-2). Direct Crossref metadata was checked on 22 September 2026: both identifiers name this paper, volume92, starting page561; one is registered by AMS and the other by JSTOR. These are alternative identifiers for the same source, not two different papers.

The paper works in the real projective plane. Property 1 gives the familiar quadratic guarantee. Its Table 1 already records the following exact projective triangle counts for the simple family, for n>=5:

| n mod 6 | Projective triangles in Table 1 |
|---|---:|
| 0 | n(n-3)/3 |
| 1,5 | (n²-3n+5)/3 |
| 2,4 | (n²-3n+8)/3 |
| 3 | (n²-3n+9)/3 |

For odd n not divisible by 3, this projective count equals G(n); for n=3 mod6 it equals G(n)+1. A projective count does not by itself imply that every counted face can remain bounded in one affine chart. Our chart argument addresses precisely that additional requirement. The source contains no explicit affine-chart version of G located in this audit. The cubic/trigonometric family must remain attributed to Füredi–Palásti.

### Erickson, 1999

[New Lower Bounds for Convex Hull Problems in Odd Dimensions](https://jeffe.cs.illinois.edu/pubs/convex.html), SIAM Journal on Computing 28(4), 1198–1214; [author manuscript, section 7.2](https://jeffe.cs.illinois.edu/pubs/pdf/convex.pdf). A conference version appeared at SoCG 1996.

Erickson describes the same line family and explicitly counts ceil(n(n-3)/3) triangles. The angle-shifting passage moves the three supporting lines of one selected triangle until they become concurrent, while preserving other triple orientations. It is used for a decision-tree lower bound for detecting affine degeneracy. It is not a universal one-line Kobon extension and does not state G(n) or the present chart refinement.

### Felsner and Kriegel, 1999

[Triangles in Euclidean Arrangements](https://page.math.tu-berlin.de/~felsner/Paper/tri.pdf), Discrete & Computational Geometry 22(3), 429–438.

The introduction distinguishes straight-line realizability from projective pseudoline constructions, and identifies Füredi–Palásti's n(n-3)/3 construction as the general straight-line baseline. Results maximizing triangles among pseudolines cannot be transferred automatically to straight lines. This paper supplies historical context, not a claim that every possible affine constant-term refinement is absent.

### Forge and Ramírez Alfonsín, 1998

[Straight Line Arrangements in the Real Projective Plane](https://doi.org/10.1007/PL00009373), Discrete & Computational Geometry 20(2), 155–161; [author-uploaded paper](https://www.researchgate.net/publication/225741288_Straight_line_arrangements_in_the_real_projective_plane).

This work supplies infinite families of extremal simple projective straight-line arrangements. It strengthens individual infinite subsequences. Its projective result is not, without an affine chart argument and interpolation, an all-n affine guarantee stronger than G.

### Harborth and Roudneff

Harborth's [Some simple arrangements of pseudolines with a maximum number of triangles](https://doi.org/10.1111/j.1749-6632.1985.tb14536.x), Annals NY Academy of Sciences 440 (1985), 31–33, and Roudneff's cited projective extremal constructions concern pseudolines. They are relevant combinatorial templates, but stretchability is a separate mathematical condition. Their role and scope are discussed in the Felsner–Kriegel paper and the BBL and Blanc papers below. We did not locate a primary statement of the affine straight-line formula G in these references; this is not an exhaustive priority clearance.

### Bartholdi, Blanc and Loisel; Blanc

[On simple arrangements of lines and pseudo-lines in P² and R² with the maximum number of triangles](https://arxiv.org/html/0706.0723v1), by Nicolas Bartholdi, Jérémy Blanc and Sébastien Loisel, and Blanc's [The best polynomial bounds for the number of triangles in a simple arrangement of n pseudo-lines](https://arxiv.org/html/0801.2845v2).

These papers provide sharper simple-arrangement upper bounds, extremal pseudoline families, and structured straight-line extension constructions. The straight-line doubling hypotheses are stronger than merely having many triangles; arbitrary pseudoline extensions need not be stretchable. Their constructions are important ingredients for the current hybrid program, but we did not locate an unconditional all-n affine formula replacing G in them.

### Damásdi, Martínez-Sandoval, Nagy and Nagy, 2020

[Triangle areas in line arrangements](https://real.mtak.hu/114794/7/1-s2.0-S0012365X20302910-main.pdf), Discrete Mathematics 343, 112105, section 3.

This modern primary-paper summary quotes floor(n(n-3)/3) as the general Kobon lower bound, credited to Füredi–Palásti, and also points to Forge–Ramírez Alfonsín. The floor is a slightly weaker rounding than B. This confirms that the classical all-n construction is established literature; it does not prove that no earlier author noticed the chart refinement. The paper's other all-n constructions concern congruent or minimum-area triangles, a different extremal objective.

## Related current research, separately scoped

[The Exact Maximum Complexity of the Affine Envelope of a Line Arrangement](https://zenodo.org/records/22135470) is a 2026 preprint with multiple revisions. The accessible [corrected intermediate record](https://zenodo.org/records/22117877) claims max H(A)=floor((7n-15)/2), with an explicit rational family and a curvature identity relating H to bounded face counts. This is an envelope theorem, not a formula for the maximum number of Kobon triangles. The newest record was identified through Zenodo's version link; its proof has not been independently audited here. Earlier versions used a different lower-bound argument, so citations must specify the version.

## Wording to avoid

* “The first lower bound valid for every n”: false in view of Füredi–Palásti.
* “The first appearance of every numerical constant in G”: the original projective table already contains related constants.
* “A universal extension of any optimal arrangement”: the new all-n construction is explicit; it does not establish such an operator.
* “A stronger bound than all published individual constructions”: G is below several known finite and infinite-subsequence records.
* “The recent affine-envelope preprint solves Kobon”: its objective and hypotheses are different.

## Remaining priority work

Before a publication claims first numerical priority for G, inspect the full relevant chapters of Grünbaum's arrangements monograph, the complete follow-up literature on affine charts of Füredi–Palásti arrangements, and any unpublished notes from active Kobon researchers. A formalization-and-explicit-refinement claim does not depend on completing that broader historical search.
