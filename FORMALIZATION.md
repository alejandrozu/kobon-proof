# What the Lean development proves

This document is a scope audit, not a declaration that the entire project is finished.

## Checked mathematical statements

| Development | Statement actually checked |
|---|---|
| `Geometry.validate_sound` | An accepted integer coordinate/list certificate supplies real, pairwise nonparallel lines and at least the stated number of distinct nondegenerate empty supporting triples. |
| `Simple.validate_simple_sound` | The same witness also has no concurrent triple, when that additional check passes. |
| `Euclidean` | Supporting intersections lie on the lines; their area determinant is nonzero; the polynomial tests have the affine signs claimed; a valid line with one weak sign on all three vertices misses the entire open barycentric interior. |
| `Certificates/*.lower_bound` | Concrete finite lower bounds for the supplied coordinates. They do not assume the original extension principle or a published infinite construction. |
| `SimpleCertificates/*.simple_lower_bound` | Concrete bounds with a simple witness; they also imply the classical lower bound. |
| `Results.classical_NNN`, `Results.simple_NNN` | The materialized 3–60 table, separately for unrestricted and simple witnesses. |
| `Results.earlier_NNN` | Every numerical row of the earlier own-results inventory, using a finite witness at least as strong. This verifies the inequality, not the originally proposed general derivation or novelty. |
| `KobonBoundary` | Cyclic mass/average identities, charging arithmetic under explicit hypotheses, odd defect-two and even boundary criteria, and equivalence of the two parity formulations. |
| `KobonExamples` | Exact small rational examples and simplicity, checked by kernel reduction. |
| `Families` | Closed forms, recurrence identities, invariant arithmetic, and displayed family values. **No existence of a line arrangement for all parameters is inferred from these arithmetic theorems.** |
| `AffineLemmas` | Affine sign stability from endpoints and preservation of a triangle by an exterior affine inequality. |

`LowerBound n T` is defined directly by line coordinates, rather than by an uninterpreted maximum function. For lines `a*x+b*y=c`, the checker uses homogeneous intersections. It rejects a concurrent supporting triple and requires every arrangement line to have one weak sign at all three vertices. Weak signs permit a line through a vertex. Multiplication by the squared nonzero pair determinant converts this polynomial sign test to the ordinary affine sign test; `orientedEval_affine` proves the identity.

The triangles are distinct supporting triples with indices `i<j<k<n`. Strictly increasing integer keys prove that the witness list has no duplicates. A supporting triple has a nonzero determinant and determines its three vertices. This is the explicit empty-triangle convention used here. A separate formal equivalence with a topological connected-component definition of arrangement cells, and a complete formal theory of cells/unused edges, have not been developed. That bridge is part of the general geometric work below.

The large Lean certificates prove **at least** the displayed count. They need not enumerate every possible supporting triple to prove a lower bound. The two Python counters independently establish the exact count of the saved arrangement. No Python assertion is treated as a Lean theorem.

## Trust and reproduction

- Pinned Lean: see `lean-toolchain`; pinned Mathlib and transitive dependencies: `lakefile.toml` and `lake-manifest.json`.
- Generic proofs use Lean's ordinary logical axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Concrete large checks use `native_decide`, whose generated native-evaluation dependencies are recorded. This adds trust in the native compiler/runtime; it is not pure kernel evaluation of all integer calculations.
- `Kobon.Audit` traverses every theorem in the project's namespaces, rejects dependencies outside the standard axioms and explicitly recognized native-evaluation certificates, and reports the trust category. In particular, any `sorryAx` dependency fails.
- `scripts/verify_lean.py` rejects placeholder, `admit`, added-axiom, and unsafe source tokens in the active library before building. It records logs and hashes, so a successful older run cannot be silently attributed to modified proof sources.
- The archived March source contains eight placeholders. It is historical evidence, excluded from the active Lake library. Removing those statements from the build is not represented as proving them.

## Unfinished obligations

1. **General exterior construction.** Define elementary segments, free rays, boundary wedges, and their cyclic directions for a real simple arrangement. Prove the ray-to-unused-edge charging map has at most two preimages per edge; prove the convex-hull lower bound of three wedges; identify the complete cyclic sector profile; and prove that the added real line creates precisely the visible wedges. Then connect those results to the existing finite counting theorems. The ordinary proof is in `research/kobon-extension/manuscript.md`.
2. **Infinite hybrid geometry.** Formalize the actual tangent constants and rational interval enclosure theorem, prove parameter-stable crossing orders and incidences, and formalize the geometric doubling/iteration theorem. The current interval program plus the cited BBL theorem provides the manuscript argument; `Families.lean` only supplies the arithmetic. A finite list of successful doublings does not discharge this obligation.
3. **The other infinite additional-line family.** Formalize the Parpalak–Utkin even-family geometry and the all-parameter extra-line step behind the 51/99/195 draft. Those finite certificates already stand independently of this claim.
4. **Published upper bounds and comparisons.** Blanc's simple upper bound, classical upper bounds, externally quoted optimality, and literature priority are cited facts rather than Lean theorems here. Consequently `44:608` is a checked simple lower bound; the equality `K_s(44)=608` additionally invokes the external upper-bound theorem.
5. **Original unrestricted full-gain claim.** No proof here establishes `K(n+1) >= K(n)+floor(n/2)` for all `n`, nor the original unrestricted odd-to-even version. The failed alternating-segment argument cannot be repaired by filling a placeholder with its conclusion as a hypothesis. A counterexample to one fixed extension method is not a counterexample to a recurrence for maxima.

Completing these items is required before describing every result in the manuscripts as self-contained Lean mathematics. The current release deliberately makes no such claim.
