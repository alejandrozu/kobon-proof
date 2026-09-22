# Local release verification

Completed 22 September 2026 at 07:18:05 UTC, within the shortened session
deadline of 07:36:37 UTC. The research source is frozen for this release.

## Checked results

- **220 of 220 Lean build targets passed**, including the root library and
  `Kobon.Audit`. The pinned toolchain is Lean 4.31.0.
- **325 active Lean source hashes matched** the files checked by the final
  build. The active source scan rejects `sorry`, `admit`, custom `axiom`
  declarations and `unsafe` definitions.
- **4,227 theorem declarations passed the axiom audit.** Of these, 3,412
  depend only on the accepted standard logical axioms; 815 also depend on
  explicitly reported native evaluation used for finite certificates.
  These are theorem counts, not counts of distinct axioms.
- **138 finite coordinate certificates passed both independent exact
  counters**; 104 are simple arrangements. Original construction authorship
  remains attached to the certificate sources.
- The separate rational interval seed check passed. Regenerating the
  parameterized seed, successor experiment, all-order finite envelope and
  result index reproduced the release. The envelope has 64 strict finite
  enhancements over the earlier classical baseline; these are not 64 new
  discoveries.
- The final **nine-page Word review** was rendered and every page visually
  inspected. Equations are editable native Word mathematics.

The authoritative machine records are
[`lean-summary.json`](../../verification/lean-summary.json),
[`coordinate-summary.json`](../../verification/coordinate-summary.json),
[`seed-interval-summary.json`](../../verification/seed-interval-summary.json),
[`report-qa.json`](../../verification/report-qa.json), and the
[`build logs`](../../verification/build-logs/). The
[`evidence manifest`](../../evidence/file-manifest.json) hashes the stable
source and research files. GitHub Actions independently reruns the proof and
coordinate checks on the uploaded commit; its live result is separate from
this completed local verification.

## Scope that remains open

The verified all-order construction and the geometric one-step BBL theorem
are completed results. This release does **not** claim a fully formal
infinite BBL iteration, an unrestricted quantitative successor recurrence,
a new unrestricted upper bound, a solution of the Kobon problem, or numerical
first priority for the affine refinement. The precise next proof tasks are
in the [iteration plan](hybrid-family/NEXT_ITERATION_PLAN.md).

The archived March proof and the explicitly unverified `TamuraSeed33` draft
are outside the active library. Large experimental coordinates outside the
138-certificate catalog have their own recorded verification status. In
particular, the second independent count at 642 lines was interrupted and
is not described as complete.

The staging whitespace check reported only a trailing blank line in
`BBLIntersection.lean` and in the preserved third-party Maiorana license;
neither is a mathematical or build failure. The external license bytes were
retained unchanged.
