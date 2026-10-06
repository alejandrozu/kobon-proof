# Boundary extension research checkpoint

Research owner: Alejandro Zarzuelo Urdiales. Session: 5–6 October 2026.
This records proof progress during the seven-hour research session; manuscript
and repository-wide integration are deferred at the author's request.

## Actual geometric counting theorem

For a nonparallel simple real arrangement with n ≥ 3, let T be the cardinality
of any finite injective family of certified bounded triangles. Define

    δ = n(n−2) − 3T.

Each line's first and last actual intersection vertices are its terminals.
Let A count vertices terminal on exactly one supporting line and B count
vertices terminal on both supporting lines. Let U be the number of actual
consecutive line segments unused by the chosen triangle family.

The following statements have compiled with standard Lean axioms only:

    A + 2B = 2n,
    A ≤ 2U,
    δ = U,
    B ≥ n − δ.

The counting proof uses the actual sorted real intersection inventory.
A single-terminal ordinary vertex has three bounded incident segments.
The used incident degree is even, since each triangle supplies zero or two
incident sides and simple arrangements have no shared triangle sides.
Consequently that vertex consumes an endpoint of an unused segment; each
unused segment supplies at most two endpoint charges.

Primary endpoints in `Kobon/OpenMathSimpleBoundary.lean`:

- `certificate_single_terminal_budget`
- `terminal_partition`
- `certificate_double_terminal_budget`
- `certificate_boundary_defect`

`Kobon/OpenMathBoundaryRays.lean` also gives an actual nonzero outward
tangent at each terminal point, proves that it avoids every forward old
transverse crossing, and derives its exact affine sign invariant.
Endpoint: `terminal_outward_signs`.

## Exterior visibility bridge

`Kobon/OpenMathBoundaryVisibility.lean` connects two supported outward
tangents with positive normal projections to the existing geometric
`Exterior.VisiblePair` predicate. It proves the derivative identity from
actual tangent vectors and handles the two supporting old lines separately.
Endpoint: `pair_visible_of_terminal_signs`.

The pair bridge and its subsequent simplification both replayed successfully
with standard axioms. `OpenMathBoundaryWitnesses.lean` supplies actual ordered
support indices, vertices and two outward tangents, and proves that the
resulting triple labels are injective. There is no visibility oracle.

## Completed geometric successor and iteration

The normal chart, exact critical roots, sector sample existence, adjacent
root counts and integer averaging have compiled modules. Their assembly in
`OpenMathBoundarySuccessor.lean` proves that each actual double-terminal
vertex is selected by exactly n−1 of the 2n actual normal choices. The
selected vertices give a list of distinct new certified triangles, and a
sufficiently distant inserted line preserves every old certified triangle
and simplicity. Consequently an exterior direction gains at least

    some exterior direction gains at least
    ceil((n−1)B/(2n)).

`OpenMathBoundaryMinimum.lean` additionally proves B≥3 for every simple
arrangement with n≥3. For each actual normal, a maximal projected old
vertex is double-terminal and both outward tangents project positively.
Thus every normal selects at least one vertex; exact counting gives
(n−1)B≥2n and hence B≥3.

The strongest completed count-only rule is therefore

    b = max(3, max(0,n−δ)),
    g(n,T) = ceil((n−1)b/(2n)),
    SimpleLowerBound(n,T) ⇒ SimpleLowerBound(n+1,T+g(n,T)), n≥3.

`OpenMathExtensionFormula.lean` proves the exact closed arithmetic form
of the same gain:

    δ = n(n−2)−3T,
    g(n,T) = min(floor(n/2), ceil(max(3,max(0,n−δ))/2)).

The natural-number subtraction in Lean truncates at zero. The displayed
minimum is an equality with the ceiling formula above, rather than a new
geometric assumption. Endpoint `closed_form_successor` gives the actual
simple straight-line successor directly with this formula.

This is proved in `OpenMathEveryOrderExtension.successor`. It works in
both parity directions. `infinite_quantitative_extension` iterates the
rule to every larger natural order from any supplied simple seed:

    T₀=T; Tₖ₊₁=Tₖ+g(n+k,Tₖ).

There is also the simpler corollary Tₖ≥T+2k for n≥4. These theorems have
fully compiled with only propext, Classical.choice and Quot.sound; they
contain no custom axioms, native computation axioms or sorry placeholders.
They assert actual arrangements of real straight lines.

For odd n=2m+1, δ≤2 forces g≥m. Endpoint
`OpenMathBoundarySuccessor.odd_defect_two_successor` is compiled. Therefore
any supplied simple arrangement attaining floor(n(n−2)/3) has a successor
attaining the rounded simple even upper bound. Both the polynomial identity
and actual simple optimality statement are compiled in
`OpenMathOptimalSuccessor.lean`.

These results do not establish optimal odd witnesses for all orders, an
unrestricted upper bound allowing multiple intersections, or the formerly
claimed half-order gain from every arbitrary input. The recurrence can
be substantially weaker than the best individual constructions and the
existing quadratic all-order baseline; its strength is its unconditional
geometric applicability and its precise dependence on the input deficit.

## Attribution

BBL2007 already describes exterior successors from affine-perfect odd
arrangements (δ=0). See `corpus/SUCCESSOR_ATTRIBUTION.md` for pinned primary
sources. All three March examples 27→28, 29→30 and33→34 have δ=0.
Near-perfect rounded-optimal inputs such as31:299 and49:767 have δ=2.
Blanc2008 also shows specific near-perfect examples7→8 and19→20. The
broader candidate contribution is the arbitrary-input deficit-dependent
theorem, its indefinite iteration, and its fully extracted Lean geometry,
rather than a new claim to those known individual counts. Priority of the
full quantitative statement remains subject to further literature review.
