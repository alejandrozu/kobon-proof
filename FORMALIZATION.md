# What the Lean development proves

This document is a scope audit, not a declaration that the entire project is finished.

## Three hour research update

`Universal.baseline_sound` now proves, for every natural `n`, a simple real-line
construction with `G(n)=floor(n(n-3)/3)+1+(n mod 2)` for `n>=4`, with zero below
three and one at three. The proof has only standard logical axioms. Its exact
gain over the old ceiling baseline, for residues 0 through 5 modulo 6, is
`1,1,0,2,0,1`. `Universal.all_n` additionally retains every finite certificate.
There are currently 138 coordinate certificates, 104 simple, and 64 strict
finite enhancements over the old baseline. First numerical priority for the
improved all-order formula is not established by formal verification.

`Cells.lean` proves that certified triangle interiors are nonempty, uncut,
equal to their arrangement sign cells, and pairwise disjoint for distinct
supporting triples. This closes the earlier geometric gap about overlapping
interiors. A full arrangement graph and global unused-edge counting theory
is still outside the development.

The `BBL` modules add actual trigonometric crossing limits, integer crossing
profiles, continuity of old triangles and visible pairs, geometric cap signs,
the count of mixed triangles, finite witness assembly, and a grid reindexing
identity. `BBLDoubling.doubling` now combines these into an actual geometric
one-step theorem: a simple seed on the prescribed tangent grid with
`0<epsilon<tan(pi/(8*r))`, with every
distinguished-line segment triangular and the central apex above that line,
gives `SimpleLowerBound (8*r+1) (T+(4*r)^2)` for every `r>=5`. Crossing order,
cap retention and the new triangles are conclusions of the construction,
not hypotheses of this final theorem. It uses only standard logical axioms.
The cumulative [review](research/six-hour-2026-09-21/RESEARCH_REVIEW.md)
records the remaining seed reindexing and invariant obligations.
End-to-end infinite iteration remains a separate goal.

`SharedFan`, `FanGeometry`, `FanCount`, and `CyclicFan` prove local real-line
incidence and fan bounds. `CleanLineBudget` proves arithmetic consequences
of explicitly supplied global charging hypotheses. This is not a formal
unrestricted improvement of the Kobon upper bound. The source audit found
an ambiguity in a literal local statement used in one upper-bound argument;
it does not establish that the final published upper bound is false.

The generated `research/six-hour-2026-09-21/drafts/TamuraSeed33.lean` candidate
was not compiled to completion and is explicitly outside the active library.
The active-module source scan and axiom audit remain mandatory. The original
March archive is likewise historical, not a completed proof.

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
| `FurediPalastiCount`, `FurediPalasti.lower_bound` | General modular counting and actual real-line geometry prove the classical ceiling baseline at every order at least three, without imported geometric assumptions or native evaluation. |
| `AllN.all_n`, `Universal.all_n` | Unconditional geometric lower-bound functions on all natural numbers; Universal adds the stronger parity-sensitive baseline and retains all 138 saved certificates. |
| `AllN.from_49_unconditional` | `LowerBound n ((n-1)^2/4+191)` for every `n >= 49`, using 49/50 certificates and the proved classical baseline; does not assume or prove the full-gain recurrence. |
| `Families` | Closed forms, recurrence identities, invariant arithmetic, and displayed family values. **No existence of a line arrangement for all parameters is inferred from these arithmetic theorems.** |
| `AffineLemmas` | Affine sign stability from endpoints and preservation of a triangle by an exterior affine inequality. |
| `Parametric` | Sound rational box certificates for whole families of real line arrangements, including an open positive exceptional parameter. |
| `TangentBounds`, `SeedFamily` | Actual trigonometric enclosures and a simple eleven-line arrangement with at least 32 certified triangles for every `0 < epsilon <= 1/100000`; nine distinguished triples; arbitrarily small valid parameters. Kernel reduction, without native evaluation. |
| `Exterior.extension` | An admissible direction and a list of visible old pairs give a real exterior extension preserving all old triangles and adding one per listed pair. An explicit safe height exists. No unconditional numerical lower bound on the list length is asserted. |
| `Iteration` | The closed formula implied by the full-gain recurrence, with that recurrence explicitly assumed; exact weaker defect-iteration values; and a resource-budget obstruction. |
| `Iteration49` | Kernel checks of five finite cyclic profile maxima. Their geometric identification is checked by the exact Python experiment, not by this Lean module. |

`LowerBound n T` is defined directly by line coordinates, rather than by an uninterpreted maximum function. For lines `a*x+b*y=c`, the checker uses homogeneous intersections. It rejects a concurrent supporting triple and requires every arrangement line to have one weak sign at all three vertices. Weak signs permit a line through a vertex. Multiplication by the squared nonzero pair determinant converts this polynomial sign test to the ordinary affine sign test; `orientedEval_affine` proves the identity.

The triangles are distinct supporting triples with indices `i<j<k<n`. Strictly increasing integer keys prove that the witness list has no duplicates. A supporting triple has a nonzero determinant and determines its three vertices. `Cells.lean` now proves the corresponding open triangle is exactly its sign cell and distinct certified triples have disjoint interiors. A full global arrangement graph and unused-edge theory remains unfinished.

The large Lean certificates prove **at least** the displayed count. They need not enumerate every possible supporting triple to prove a lower bound. The two Python counters independently establish the exact count of the saved arrangement. No Python assertion is treated as a Lean theorem.

## Trust and reproduction

- Pinned Lean: see `lean-toolchain`; pinned Mathlib and transitive dependencies: `lakefile.toml` and `lake-manifest.json`.
- Generic proofs use Lean's ordinary logical axioms (`propext`, `Classical.choice`, `Quot.sound`).
- Concrete large checks use `native_decide`, whose generated native-evaluation dependencies are recorded. This adds trust in the native compiler/runtime; it is not pure kernel evaluation of all integer calculations.
- `Kobon.Audit` traverses every theorem in the project's namespaces, rejects dependencies outside the standard axioms and explicitly recognized native-evaluation certificates, and reports the trust category. In particular, any `sorryAx` dependency fails.
- `scripts/verify_lean.py` rejects placeholder, `admit`, added-axiom, and unsafe source tokens in the active library before building. It records logs and hashes, so a successful older run cannot be silently attributed to modified proof sources.
- The archived March source contains eight placeholders. It is historical evidence, excluded from the active Lake library. Removing those statements from the build is not represented as proving them.

## Unfinished obligations

1. **Quantitative exterior construction.** `Exterior.extension` now proves the real construction from algebraically certified visible pairs. Still define elementary segments, free rays, boundary wedges, and their cyclic directions; prove the ray-to-unused-edge charging map and the three-wedge lower bound; and connect the complete sector profile to the visible-pair certificates. The ordinary proof is in `research/kobon-extension/manuscript.md`.
2. **Infinite hybrid geometry.** The actual tangent bounds and real-parameter seeds are proved. `BBLDoubling.doubling` now proves the full geometric one-step gain for a compatible saturated grid seed with `q=4r>=20`. The seed-sorting permutation, preservation of the full recursive shape/visibility invariant, and connection to `Families.lean` remain unfinished. A finite list of successful doublings does not discharge this obligation.
3. **The other infinite additional-line family.** Its all-parameter geometry is not formalized. The finite certificates stand independently, and the stronger universal formula already dominates the older 51/99/195 numerical values, so this separate family is no longer required for those inequalities.
4. **Published upper bounds and comparisons.** Blanc's simple upper bound, classical upper bounds, externally quoted optimality, and literature priority are cited facts rather than Lean theorems here. Consequently `44:608` is a checked simple lower bound; the equality `K_s(44)=608` additionally invokes the external upper-bound theorem.
5. **Original unrestricted full-gain claim.** No proof here establishes `K(n+1) >= K(n)+floor(n/2)` for all `n`, nor the original unrestricted odd-to-even version. The failed alternating-segment argument cannot be repaired by filling a placeholder with its conclusion as a hypothesis. A counterexample to one fixed extension method is not a counterexample to a recurrence for maxima.

Completing these items is required before describing every result in the manuscripts as self-contained Lean mathematics. The current release deliberately makes no such claim.

`Iteration.from_49_conditional` explicitly assumes `FullStepClaim K`; it cannot be cited as a proof of that premise. The same numerical lower-bound formula now has a separate unconditional geometric proof in `AllN.from_49_unconditional`, which uses the classical construction from order 51 onward. This does not establish the recurrence. The exterior wedge budget obstructs indefinite full-gain iteration by that method, but does not refute the recurrence for maxima using interior additions or reconstructed arrangements. See [the successor report](research/successor-formalization/README.md) for the exact distinction and all source-to-theorem mappings.
