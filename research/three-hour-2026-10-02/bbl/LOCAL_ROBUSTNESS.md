# The ten-sign obstruction persists under nonuniform perturbations

This is an exact computer-assisted extension of the kernel-checked
`BBLGridObstruction.actual_grid_orientation_impossible` theorem. The interval
calculation itself is not yet formalized in Lean. It is reproduced by
`verify_local_robustness.py` using only Python's standard library and exact
rational arithmetic.

## Statement

Use the ten signed triples in `TANGENT_OBSTRUCTION.md`. Let `a_i^*` denote
the corresponding actual tangent-grid intercepts, and let

`S={0,3,6,7,8,11,13,14,15,17,19}`.

If arbitrary real intercepts satisfy

`|a_i-a_i^*| <= 1/1000` for every `i` in `S`,

then no real reciprocal-slope assignment `v_i` realizes all ten prescribed
strict determinant signs for the lines `x-v_i*y=a_i`.

The other intercepts, including the central pair, are unrestricted because
they do not occur in these ten rows. This is a statement in the specified
normalized coordinate chart. No optimality or classification assumption is
needed, and no claim concerning every possible chart is made.

## Exact reduction

Let `A` be the ten-by-twenty signed coefficient matrix. Each row satisfies
the two polynomial identities

`sum_j A_ij=0`,

`sum_j A_ij*a_j=0`.

Only the eleven columns indexed by `S` can be nonzero. Fix the last weight
to one. Solve the nine weighted-column equations corresponding to

`S \ {0,19} = {3,6,7,8,11,13,14,15,17}`

for the first nine weights. If the resulting column residuals vanish there,
the two displayed row identities give

`R_0+R_19=0`, `a_0*R_0+a_19*R_19=0`.

The interval boxes ensure `a_0<a_19`, so both remaining residuals vanish.
The generic `BBLObstructionReduction.two_columns_follow` and
`reduced_infeasible` statements formalize this algebraic reduction; their
hypotheses still require the weighted equations and signs to be established.
They do not implicitly assert the correctness of the external interval audit.

## Interval certificate

The actual root `t=tan(pi/20)` lies between the consecutive rational bounds

`158384440324536293838883092694 / 10^30`

and

`158384440324536293838883092695 / 10^30`.

These same bounds are already proved by `BBLTangentBounds.tan_1_bounds`.
The script also checks, in exact rational arithmetic, opposite signs of the
quartic at the two endpoints and containment in the isolating interval.
The exact polynomial formulas from `BBLTangentValues` enclose each `a_i^*`;
the independent radius `1/1000` is then added to its enclosure.

The verifier performs Gaussian elimination on the nine-by-nine transposed
system, selecting a fixed row-pivot order from the interval midpoints. Every
pivot interval excludes zero. Every arithmetic operation, including division,
is rounded outward to a dyadic grid of denominator `2^120`, using exact
integer arithmetic. Therefore the calculation encloses the actual elimination
and solution for every intercept tuple in the whole box, despite correlations
between the matrix entries.

The computed weights are all strictly positive; their smallest certified
lower bound is greater than `0.08692`. Thus every tuple has an actual positive
dependence with zero weighted coefficients. Multiplying ten putative strict
inequalities by these weights and adding would give `0>0`.

The complete rational interval endpoints, pivot order, pivot enclosures,
weight enclosures, and source-data hash are saved in `local-robustness.json`.
The verifier runs in well under one second on the research host. Wider boxes
of radii `1/100` and `1/10` were not certified by this calculation; this does
not establish feasibility or a sharp transition at either radius.

## Research implication

For this specific orientation pattern, merely making the tangent marks
slightly nonuniform cannot fix the obstruction. At least one of the eleven
marks must leave the radius-`1/1000` box, or the prescribed sign pattern must
change. The result supplies a quantitative exclusion region for a future
search over relaxed grids. It is not a global obstruction to optimal seeds,
nor a new numerical Kobon upper bound.
