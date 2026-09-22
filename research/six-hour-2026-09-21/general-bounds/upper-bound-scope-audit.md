# Upper-bound source audit and research implications

Research date: 21 September 2026, America/Los_Angeles; web checks on 22 September UTC.

## Main finding

The frequently quoted even-order bound `floor(n(n-7/3)/3)` is a theorem about **simple affine pseudoline arrangements** in Bartholdi–Blanc–Loisel. Its cited theorem does not cover arbitrary multiple intersections. Blanc's later, stronger even-order polynomial also requires simplicity. We must retain those hypotheses when comparing with nonsimple Kobon constructions.

This is a source-scope correction, not a claim that a current OEIS value is false or that no other upper proof exists. The present audit did not recover an independent unrestricted theorem establishing all the smaller even-order upper entries displayed by OEIS. No edit or message was sent to OEIS or any researcher.

## Sources and exact scope

1. [Bartholdi–Blanc–Loisel, 2007](https://arxiv.org/html/0706.0723v1), introduction and Theorem 1.1: the authors restrict the paper to simple arrangements, and the theorem bounds the maximum for simple affine pseudolines by `floor(n(n-7/3)/3)`. The proof begins with a simple arrangement and uses the fact that a bounded segment cannot bound two triangles. Multiple intersections can invalidate that last property.
2. [Blanc, 2008](https://arxiv.org/html/0801.2845v2), Theorem 1 and Proposition 2.0.3: the later residue-dependent bounds are also simple-arrangement statements. For even n, the common polynomial is `floor(n(n-5/2)/3)`, with the displayed residue rounding. At 44 it yields 608 for the simple variant.
3. [Clément–Bader, December 2007 draft](https://sop.tik.ee.ethz.ch/publicationListFiles/cb2007a.pdf), Theorem 1 and equation (2): the stated classical bound is `floor(n(n-2)/3)-1` when `n mod 6` is 0 or 2, and Tamura's integer bound otherwise. This is a distinct, weaker reported theorem from BBL's simple bound. The draft is an external source; its geometric argument has not been formalized or independently re-proved here. A local wording issue in Lemma 1 is detailed below, so this column is explicitly a source-reported envelope rather than a completed proof audit.
4. [OEIS A006066](https://oeis.org/A006066), current formula and table: the page quotes the BBL even polynomial in the classical sequence and gives sharper individual even-order upper entries. Its nonsimple 14-line construction proves a lower bound of 54; applying BBL's simple theorem to it is not a valid optimality proof. An independent unrestricted proof would resolve the source gap.
5. [Savchuk, 2025](https://arxiv.org/html/2507.07951v1), Section 3: the 11-line exclusion is a separate computation. The SAT encoding excludes a perfect 33-triangle arrangement, using the equality-to-perfect reduction cited from Clément–Bader. That external SAT run was not replayed in this session. It should be distinguished from a blanket even-order theorem.
6. [ProofAtlas Kobon research page](https://www.proofatlas.ai/collaboration/kobon-triangle-problem/), status checked 7 September 2026: the page explicitly leaves the unrestricted problem open. It reports a 14-line upper bound of 54 only for arrangements with at most four finite multiple points, and warns against extending a complete-core theorem to a subgraph of a larger core. This is a research-packet summary; its underlying proofs and programs were not independently reproduced here.

The accompanying [3–60 table](upper-scope-table.md) and JSON preserve these distinctions. Their generator is `experiments/2026-09-21/general-bounds/upper_scope_table.py`.

## Examples that matter for this project

| n | Classical Clément–Bader envelope | BBL simple bound | Blanc simple bound | OEIS upper currently reported |
|---:|---:|---:|---:|---:|
| 14 | 55 | 54 | 53 | 54 |
| 20 | 119 | 117 | 116 | 117 |
| 22 | 146 | 144 | 143 | 144 |
| 28 | 242 | 239 | 238 | 239 |
| 44 | 615 | 611 | 608 | unlisted |
| 50 | 799 | 794 | 791 | 794 |

The table does not withdraw any coordinate lower bound. Our 44:608 simple certificate still matches Blanc's simple upper bound. Our nonsimple certificates remain valid lower bounds for the unrestricted problem. Claims that a nonsimple construction closes the classical gap need an upper theorem valid for that same class.

For odd orders where a retained straight-line witness meets Tamura's polynomial, this particular simple-versus-classical issue does not change the displayed numerical comparison. It also does not prove the upper polynomial in Lean.

## New research target

A genuinely unrestricted even-order improvement would be valuable. One possible route is to quantify how multiple intersections trade lost elementary segments against sides shared by two triangles, and then combine that budget with parity obstructions. The exact identity derived in `multiplicity-budget.md` makes that tradeoff explicit. It does not by itself justify BBL's polynomial for nonsimple arrangements.

The report should not describe an unlocated proof as nonexistent, or promote a source-reported bound to an independently verified theorem. A careful next audit would locate the earliest unrestricted arguments for the individual even values and replay their exclusions with complete multiplicity and parallel-line coverage.

## A local reading of Clément–Bader Lemma 1 needs care

In the [OEIS-hosted PDF](https://oeis.org/A006066/a006066.pdf), page 2, Lemma 1's numbered item 3 says a multiple intersection is “part of at most two pairs of triangles that share a common side”. Read literally as counting all shared segments incident to a multiple point, this is false. An exact counterexample is a triangle and its three medians: its center is a triple point incident to six shared segments. The saved [six-line certificate](shared-fan-six-lines.json) uses the lines

`x=0, y=0, x+y=3, x-y=0, 2x+y=3, x+2y=3`.

All six are pairwise nonparallel. The exact counter finds six bounded triangles and four triple points. At the center, D1=3 and D2=3 locally; globally D1=3 and D2=3. The total arrangement still has only six triangles, below the seven-triangle classical bound for six lines. Therefore **this example does not refute the final upper theorem**. A possible intended assignment of a shared segment to one of its endpoints would need a separate global proof; the quoted local wording and Figure 2 do not specify such an assignment. No assertion is made that a corrected proof or a different source cannot supply it.

The reproducible check is `experiments/2026-09-21/general-bounds/shared_fan_counterexample.py`. `Kobon/SharedFan.lean` now verifies the six real triangles, their disjoint uncut interiors, the six distinct elementary radial segments, and the fact that each is a side of two distinct triangles. It compiled using only the standard axioms propext, Classical.choice and Quot.sound; no `sorry` or native-check axiom occurs. This observation explains why our own core-budget proof counts D1 and D2 separately and keeps its geometric hypotheses explicit.
