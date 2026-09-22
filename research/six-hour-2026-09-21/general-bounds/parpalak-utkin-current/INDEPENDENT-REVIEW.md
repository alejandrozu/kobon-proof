# Current Parpalak–Utkin gallery: independent exact recount

The files in this folder reproduce mathematical coordinate data from the [published gallery of Roman Parpalak and Denis Utkin](https://github.com/ud1/kobon-solutions). Original discovery attributions remain those given by the gallery and [OEIS A006066](https://oeis.org/A006066); in particular, the classical eight-line record predates this gallery. These are **external constructions**, not newly discovered bounds of this project.

The immutable source commit, commit date, original paths and SHA256 digests are in `verification.json`. Original source certificates are named `upstream-NNN.json`; `certificate-NNN.json` adds independent triangle lists and provenance metadata. No upstream program was executed.

On 22 September 2026 we checked every listed face using two exact methods: elementary-segment adjacency and a separate open-interior determinant-sign test. Both methods agree on the full triangle set, not only its cardinality.

| Lines | Verified triangles | Triple points | Other finite multiple points | Parallel pairs |
|---:|---:|---:|---:|---:|
| 8 | 15 | 2 | 0 | 0 |
| 14 | 54 | 5 | 0 | 0 |
| 20 | 117 | 6 | 0 | 0 |
| 26 | 204 | 2 | 0 | 0 |
| 32 | 315 | 4 | 0 | 0 |
| 36 | 402 | 0 | 0 | 0 |
| 38 | 450 | 3 | 0 | 0 |
| 42 | 553 | 0 | 0 | 0 |
| 46 | 667 | 0 | 0 | 0 |
| 50 | 792 | 2 | 0 | 0 |

Every nonsimple witness in this selection has all its triple points on a single arrangement line. At each such point exactly two shared elementary segments have ordinary other endpoints; no shared segment has two multiple endpoints. This is a property of these witnesses, not a general theorem.

Removing the common line gives the triangle counts recorded in `common-line-deletion.json`. At8,14,20 and32 the remaining odd arrangement is optimal with11,47,107 and299 triangles, respectively. At26,38 and50 the remaining counts are182,417 and746, so their improvements should not be described as applications of a universal extension of an optimal odd arrangement.

These data establish the stated lower bounds. Neither the source's upper-bound labels nor unrestricted optimality are proved by a coordinate recount. Our separate upper-scope audit retains the hypotheses of the published upper theorems.

Reproduce with:

```text
python experiments/2026-09-21/general-bounds/check_pu_current.py
```
