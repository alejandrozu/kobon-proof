# Uncompleted concrete seed bridges

These sources are outside the active Lean library and its verified source
manifest. They are preserved to make the unfinished work reproducible.

## 33-line branch

The compact rational seed generator passed its independent exact Python
triangle, simplicity and visibility box checks. A separate directions-only
Lean probe passed. The complete `TamuraSeed33` build was interrupted after
approximately 49 minutes without a completed compiler result. Its normalized
and visible bridges were source-reviewed but could not be compiled against
an exported base theorem. No mathematical counterexample was found; this is
an uncompleted proof check, not a proved impossibility.

The internal name `TamuraSeed33` is historical. The classical dyadic perfect
family retains its attribution to Forge–Ramírez Alfonsín. The active
`BBLForgeConditional` module proves its count formulas and their geometric
consequences with the uniform seed premise explicitly supplied. It does not
discharge that premise using these drafts.

`scripts/generate_recursive_seed33.py` regenerates the compact base here.
To resume, profile the individual finite checks and analytic parameter-box
bridge, then compile all three modules before moving them into `Kobon/` and
the release build. `ParametricCached` offers a verified alternative check
implementation, but no performance improvement was established for this
33-line draft during the session.

## 49-line branch

The five files `BBLSeed49.lean`, `BBLSeed49Normalized.lean`,
`BBLSeed49Exterior.lean`, `BBLSeed49Visible.lean`, and
`BBL49VerifiedFamilies.lean` are one dependency chain. The full base check was
stopped at 19:12 UTC on 2 October after approximately 30 minutes without a
completed compiler result. The dependent files therefore have no completed
full Lean check either. All five were moved here before the release audit.

Independent exact rational interval checks passed for the uniform 49-line
seed, its exterior visibility, and the generated Lean data export. The actual
tangent bounds, copied graph identity, central-apex positivity, and count
formulas were separately checked in Lean. Those partial checks do not certify
the whole chain. See [the status note](../bbl/SEED49_STATUS.md) and its linked
evidence. No numerical record beyond the known BBL family is claimed.

`scripts/generate_recursive_seed49.py` and
`scripts/generate_recursive_seed49_exterior.py` now write their outputs here.
Resume by splitting and profiling the large native finite checks, then compile
the full dependency chain before promoting any source to the active library.
