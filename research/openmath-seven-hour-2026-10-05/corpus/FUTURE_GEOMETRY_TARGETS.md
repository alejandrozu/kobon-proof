# Follow-up targets after the verified cone and surgery tools

These are research directions, not proved results. Completed statements and
their source/build hashes are in `VERIFICATION.json`.

## Completed correction improvement and remaining targets

The initial N13 theorem excluded three antipodal full neighbors. The final
session **also excluded two**, by actual cap/support exhaustion in all six
normalized cases. `UpperOpenMathN13ActualNoDouble.lean` and
`UpperOpenMathN13Curvature.lean` are the completed geometric/counting entry
points. The bounded completion screen had previously tried
67,437 proposals from three fixed stars, found 25,753 all-triple nonparallel
cases and 36 exact two-star arrangements, but no N13 with two such neighbors.
The screen itself was not an all-order exclusion; the final theorem is a
separate kernel-checked argument. Exact two-star coordinates and radial
profiles remain in `two-antipodal-star-candidates.json` as research evidence.

The other degree-four recipient bottleneck has now been resolved:
`UpperOpenMathNonfullAntipodalRecipients.lean` proves at most two incident
antipodal neighbors for every all-triple recipient with total shared degree
at most four, including `(a,d)=(0,4)`. The N13 bound of one now has its separate
proof. `UpperOpenMathN12Recipient.lean` further gives at most one antipodal
neighbor for `(1,2)` recipients, adding a positive boundary charge.

Preserving an existing full star also preserves its nearest core endpoints.
Consequently, adding lines after two stars already have disjoint neighbor
sets is a poor way to force a common recipient. A more targeted construction
should grow the second star around a prescribed old outer core from the
start, while retaining the three existing supports of that common triple.

The abstract seven-vertex half-charging sharpness graph had two antipodal
stars with the same four neighbors. The actual center-uniqueness theorem
excludes that realization. It does not by itself exclude other larger
graphs saturating the finite charging inequalities. A global improvement
must exploit additional actual incidence constraints, not infer geometric
sharpness from the finite graph alone. The resulting source-free correction
is now verified; the remaining general geometric correction is concentrated
at full `(1,5)` cores and at higher-multiplicity classes outside the all-triple
theorem. This remains a structural research direction, not a solved
unrestricted numerical upper bound.

Antipodal-to-marked-full and antipodal-to-full-one-cap adjacencies really
occur. Their exact witnesses are retained here. In particular, an attempted
discharge must not silently assume independence from every full negative
local type. The four-neighbor uniqueness theorem is a distinct resource and
allows higher multiplicity at other cores.

## Completing the local translation classification

The generic certifier already proves eventual exact triangle counts and,
with one isolated old triple, exactly one birth and the exact birth/loss
identity. It does not yet prove a global alternating-sector loss theorem.
The six-line interval witness shows that three old triangles can be lost in
one direction, and reversing the resolution can gain two. A restriction to
at most two broken sectors is therefore false.

A promising next lemma classifies the two opposite translations jointly:
each old triangle away from the unique triple should survive both, and each
old triangle incident at that triple should survive exactly one direction.
The intended local count identity would then relate the sum of the two
resolved counts to the old count and the number of triangles at the core.
This statement remains unproved here; the exact germ certifier can check
proposed witnesses without importing the incorrect half-plane count from
the audited preprint.

## Construction searches worth changing structurally

The retained fixed-angle LP and fixed-backbone corridor failures only rule
out the tested types and margins. Uniform seeds permit coefficients depending
on epsilon; the constant reciprocal-slope fits were a sufficient condition.
Future symbolic or Puiseux fits should distinguish that flexibility explicitly
and require an actual parameter interval certificate before claiming a
family. The existing kernel rational tangent certifier is reusable for new
denominators and arbitrary finite Taylor orders.

The successful 61-line Pareto construction and 37-line uniform bridge are
owned by the construction branch. Their exact interval and Lean records are
the starting points for further face/visibility improvements. Repeating
small dominated source records or another fixed chart screen is lower
priority than finding a preserved geometric invariant for a new recurrence.
