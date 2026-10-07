# Exact scope of the half-plane yield audit

Youming Liu's *Triangular cells and the classical Kobon count: a
desingularization calculus*, Zenodo record21181452, version1 (posted July3,
2026; PDF dated June29), Theorem1.1 on printed page2 defines its local count
using triangles “whose interior lies in Hᵢ” and states
`T(A′)=T(A)+1−τᵢ`. Its hypotheses include an isolated triple point with all
other vertices ordinary. Source: https://doi.org/10.5281/zenodo.21181452.

The four lines `y=0`, `y=x`, `y=−x`, `2x+y=2` meet those hypotheses. Their
two triangles have supporting triples013 and023, and both interiors satisfy
`x−y>0`. Replacing `y=x` by `y=x+ε` moves into `x−y<0`, so the stated
half-plane count is0. Nevertheless, for every `0<ε<1` the shifted
arrangement has exactly2 triangles, with supporting triples012 and023.
The claimed formula predicts3. This refutes that formula within its stated
scope; it says nothing about unrelated results in the same preprint.

All of these assertions, including the whole open interval and positivity
throughout each old triangle interior, are proved in
`Kobon/OpenMathFourLineResolution.lean`, with standard logical axioms only.
The independent finite ledger is retained alongside the Lean proof.

A separate six-line witness shows why replacing the count by a restriction
to at most two broken sectors would also be wrong. Three old triangles
occupy alternating sectors0,2,4. Upward motion retains them and adds one;
downward motion loses all three and adds one. The latter reversed operation
gains2. Its exact interval proof is in
`Kobon/OpenMathSixLineResolution.lean`; consult its completed build log
before treating it as verified. No general surgery theorem is imported.

Liu's earlier weighted-boundary paper (Zenodo20969174, June27,2026)
studies bounded-edge incidences with unbounded cells. That quantity differs
from our double-terminal visibility witnesses; its Euler identity does not
establish our quantitative successor theorem.
