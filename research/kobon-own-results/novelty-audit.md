# Priority audit of the omitted Kobon bounds

20 September 2026

The preceding inventory recorded outputs of our calculations. It did not establish that those outputs were original numerical records. This audit distinguishes explicit domination by older constructions, a known matching result, and unresolved candidates. No additional first-discovery claim has been established.

## Five candidates remaining after the comparisons made here

The baseline below is a verified value supplied by the old Füredi–Palásti construction. It is **not asserted to be the best value obtainable from every earlier construction**.

| Lines | Our bound | Verified older-construction baseline | Difference over that baseline |
|---:|---:|---:|---:|
| 39 | 469 | 468 | +1 |
| 44 | 608 | 602 | +6 |
| 51 | 817 | 816 | +1 |
| 99 | 3169 | 3168 | +1 |
| 195 | 12481 | 12480 | +1 |

The 39-line result adds a line to the published Parpalak–Utkin 38-line arrangement. The 51-, 99-, and 195-line results come from the same additional-line family applied to the Parpalak–Utkin even family. Those underlying constructions retain their attribution.

For 44 lines, this audit materialized the previous theorem consequence as an exact rational certificate: the published 43-line arrangement has 587 triangles, and our exterior line creates 21 more while preserving every old triangle. Both exact counters report 608, and the arrangement is simple. Blanc's bound for simple affine arrangements with n congruent to 2 modulo 6 is (n(n-5/2)-2)/3; at n=44 this equals 608. Consequently the certificate proves K_s(44)=608. This is an exact statement about the simple variant, not an upper bound of 608 for unrestricted classical K(44). It also does not establish first discovery of the 44-line construction or its numerical consequence.

The candidate certificate is [certificates/n044.json](certificates/n044.json); its verification record is [verification_n044.json](verification_n044.json). Other candidate certificates are in the same directory.

## Eleven omitted rows already dominated

| Lines | Our output | Stronger existing construction available |
|---:|---:|---:|
| 40 | 470 | 494 |
| 47 | 679 | 690 |
| 48 | 715 | 720 |
| 52 | 818 | 850 |
| 53 | 852 | 884 |
| 54 | 886 | 918 |
| 55 | 920 | 954 |
| 56 | 956 | 990 |
| 57 | 992 | 1045 |
| 59 | 1088 | 1102 |
| 60 | 1104 | 1140 |

Except at 57, the comparison values were obtained from rational realizations of the classical Füredi–Palásti construction and checked by independent adjacency and open-interior-sign counters. The bound 1045 at 57 lines belongs to the BBL family 14*2^t+1 and meets the classical upper bound.

## A matching bound already implicit in 2007

The value K(58)>=1073 is not a new numerical claim: BBL's straight-line family includes a perfect 57-line arrangement with 1045 triangles, and the perfect-odd exterior-line extension discussed in that paper adds 28. This gives 1073 without the new defect theorem.

## What the search establishes and what it does not

The audit checked the 1984 Füredi–Palásti construction, the 2007 BBL and 2008 Blanc papers, the 2026 Parpalak–Utkin paper and public even-family draft, the two public galleries, and targeted searches for the candidate orders and counts. No earlier explicit equal-or-better straight-line result was identified for the five candidates in this audit. Failure to find one is not proof of priority; implicit consequences, other constructions, and unindexed work remain possible.

Exploratory chart sampling of the nonsimple Füredi–Palásti example did not improve its usual affine count in the tested samples. This was a bounded numerical search, not an exhaustive result or an upper-bound proof, and is not used to claim that the five candidates are records.

The general defect theorem still has ordinary geometric proofs with a Lean-checked counting core, rather than end-to-end Lean geometry. The separate infinite odd-family argument remains a draft argument; the finite certificates stand independently of that argument.

## Earlier OEIS attribution versus priority

OEIS currently credits Zarzuelo at n=28,30,34. That attribution alone does not establish first discovery. In particular, the BBL 2007 table already lists 275 at n=30 in bold, its notation for a stretchable arrangement. The n=34 value 357 also follows from its perfect straight-line 33-line family and its stated exterior extension. The attribution and the novelty of the formulation should therefore be discussed separately.

## Sources

- [Füredi–Palásti (1984), Arrangements of Lines with a Large Number of Triangles](https://paperzz.com/doc/9476977/arrangements-of-lines-with-a-large-number-of-triangles). The finite affine realizations used in this comparison are reproductions, not claimed new constructions.
- [Bartholdi–Blanc–Loisel (2007)](https://arxiv.org/html/0706.0723v1), Theorem 1.3, paragraph following Theorem 1.1, and Theorem 1.4 table.
- [Blanc (2008)](https://arxiv.org/html/0801.2845v2), Theorem 1 and Sections 5–6. Pseudoline constructions alone are not treated as straight-line lower bounds.
- [Parpalak–Utkin (2026)](https://arxiv.org/abs/2604.22035).
- [Parpalak–Utkin even-family draft](https://github.com/parpalak/kobon-even-draft/blob/master/8-14-26-even-series.md).
- [Public exact gallery certificates](https://github.com/ud1/kobon-solutions/tree/master/gallery/certificates).
- [Parpalak–Utkin gallery index](https://raw.githubusercontent.com/parpalak/triangle-maximal-18-series/master/gallery/index.json).
- [OEIS A006066](https://oeis.org/A006066).

No external edits, publication submissions, or messages to researchers were made.
