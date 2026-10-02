# Isolated checks retained for reproducibility

These self-contained Lean inputs preserve partial checks used during the seed
investigation. They are outside the active library because they copy literal
seed definitions in temporary namespaces, rather than importing a completed
seed theorem.

- `BBLSeed49GraphCheck.lean` proves the copied graph identity and positive
  central-apex expression. It does not prove simplicity or triangle validity.
- `BBL49ArithmeticCheck.lean` proves the target count formula and polynomial
  comparisons. It does not prove geometric existence.
- `TamuraSeed33DirectionsProbe.lean` proves pairwise nonparallel directions
  using native evaluation. It does not check triangles or the full parameter
  box. The historical filename does not assign numerical priority to Tamura.

From the repository root, after building the active library, each can be
checked with `lake env lean research/three-hour-2026-10-02/bbl/checks/FILE.lean`.
`summary.json` records the separate replay hashes and compiler outcomes.
These files are not substitutes for the full archived seed chains.
