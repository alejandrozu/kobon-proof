# Strongest outputs of our Kobon work

20 September 2026. The range is 3–60, followed by the larger exact certificates.

These are outputs of our extension rule or our explicit construction steps. Published arrangements used as inputs retain their original attribution. Unchanged literature records and comparison-seed reproductions are excluded. This is not a claim that the numerical bounds are new records or were first discovered here.

**G:** numerical consequence of the geometric defect theorem, using an available simple input. **C:** explicit exact certificate. **B:** elementary base example.

| n | Strongest output: K(n) at least | Evidence |
|---:|---:|:---|
| 3 | 1 | B |
| 4 | 2 | G |
| 5 | 5 | B/C |
| 6 | 7 | C |
| 7 | 10 | C |
| 8 | 14 | G |
| 9 | 19 | C |
| 10 | 25 | G |
| 11 | 28 | G |
| 12 | 36 | G |
| 13 | 39 | G |
| 14 | 53 | G |
| 15 | 61 | C |
| 16 | 72 | G |
| 17 | 76 | G |
| 18 | 93 | G |
| 19 | 98 | G |
| 20 | 116 | C |
| 21 | 127 | C |
| 22 | 143 | G |
| 23 | 149 | G |
| 24 | 172 | G |
| 25 | 178 | G |
| 26 | 203 | G |
| 27 | 217 | C |
| 28 | 238 | G |
| 29 | 245 | G |
| 30 | 275 | G |
| 31 | 283 | G |
| 32 | 314 | G |
| 33 | 331 | C |
| 34 | 357 | G |
| 35 | 366 | G |
| 36 | 402 | G |
| 37 | 411 | G |
| 38 | 449 | G |
| 39 | 469 | C |
| 40 | 470 | G |
| 41 | 496 | G |
| 42 | 553 | G |
| 43 | 564 | G |
| 44 | 608 | C |
| 45 | 618 | G |
| 46 | 667 | G |
| 47 | 679 | G |
| 48 | 715 | C |
| 49 | 722 | G |
| 50 | 791 | G |
| 51 | 817 | C |
| 52 | 818 | G |
| 53 | 852 | G |
| 54 | 886 | G |
| 55 | 920 | G |
| 56 | 956 | G |
| 57 | 992 | G |
| 58 | 1073 | G |
| 59 | 1088 | G |
| 60 | 1104 | G |
| 99 | 3169 | C |
| 195 | 12481 | C |

The 39-line certificate gives 469, correcting the 468 retained in the earlier comparison. The stronger special outputs at 7, 9, 15, 21, 27, 33, 39, 48, and 51 lines were not all represented by the general-rule E column.

The explicit outputs at 9, 15, 21, 27, 33, 39, 48, 51, 99, and 195 lines permit triple intersections. They are classical Kobon bounds and cannot be fed into the simple-arrangement defect formula without a separate simplicity check.

The earlier infinite-family argument gives K(q+3) >= q^2/3 + q + 1 for q=6*2^t, t>=0, by adding a line to the Parpalak–Utkin even family. The proof argument is in ../kobon-research/proof_note.md; its finite members at 51, 99, and 195 are exact certificates.

The simple even corollaries and general extension theorem are in ../kobon-extension/manuscript.md. In particular, for q=6*2^t or q=18*2^t, the bound at q+2 is q^2/3 + q/2 - 1. The perfect BBL q=14*2^t family gives (q^2-1)/3 + q/2 at q+2. These are deductions from attributed input families; novelty is not established.

The general geometry is proved in ordinary mathematics in the manuscript; its Lean verification covers the finite counting core, not end-to-end Euclidean formalization.

The per-row input counts, certificate locations, and hashes are in inventory.json.

An exact 44-line certificate was added during the priority audit. See [novelty-audit.md](novelty-audit.md) for the distinction between old, dominated, and still-unresolved priority candidates.
