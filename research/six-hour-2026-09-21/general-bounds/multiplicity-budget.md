# An exact budget for multiple intersections and shared triangle sides

This elementary counting identity is a research tool, not a new universal upper bound. It records explicitly the term that prevents importing a simple-arrangement argument unchanged into the unrestricted problem.

Consider n distinct affine lines. Assume each line meets at least one other line; this includes every pairwise nonparallel arrangement with n at least two. Let P be the number of parallel pairs and let t_r count finite points incident to exactly r lines. Write E for the number of bounded elementary segments, U for segments belonging to no triangular face, D for segments belonging to two triangular faces, and T for all bounded triangular faces. Define

`S = sum_{r>=3} r(r-2)t_r`.

Then

`E = n(n-2) - 2P - S`,

`3T = E-U+D`,

and therefore

**`n(n-2)-3T = 2P+S+U-D`.**

Proof: the incidence count on all lines gives `E = sum_r r*t_r - n`. The pair-intersection count gives `n(n-1)-2P = sum_r r(r-1)t_r`. Subtraction yields the first identity. Each elementary segment belongs to zero, one, or two triangular faces, which gives the second. No inequality about D is assumed.

For an arrangement containing lines with no finite intersection, replace the first subtracted n by q, the number of lines that meet another line. The fully general identity becomes `n(n-2)-3T = 2P+S+q-n+U-D`.

In a simple arrangement P=S=D=0, so the defect is exactly U. That special case is the unused-segment budget in the existing boundary manuscript. At a triple point the concurrency term contributes 3; at a fourfold point it contributes 8; higher multiplicity r contributes r(r-2). A double-used side offsets one unit of that loss. To prove a stronger unrestricted bound, one must control the combined expression `2P+S+U-D`, rather than treating D as zero.

## Exact checks

`experiments/2026-09-21/general-bounds/multiplicity_budget.py` reconstructs the exact vertices, elementary segments, and all triangles of each indexed rational certificate, then checks both identities separately. It does not infer validity from the formula alone. The associated JSON reports each multiplicity distribution, unused count, double-used count, and defect.

This is ordinary combinatorial geometry. The present repository does not yet formalize elementary segments and all face incidences in Lean, so these geometric identities have not been promoted as unconditional Lean theorems. An abstract arithmetic consequence with incidence-count hypotheses would be weaker and must be labeled accordingly.

## A useful limitation

The concurrency penalty alone gives no upper bound stronger than Tamura: the nonnegative variable D occurs with the opposite sign, and it may be large. Local arguments that count only an isolated multiple point can miss side-sharing between neighboring multiple points. The shared-side graph, global incidence relations, and parity constraints are the remaining information needed for an effective upper theorem. The identity supports a constrained search or a discharging argument; it does not complete one.
