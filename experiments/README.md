# Frozen research experiments

`2026-09-20/` preserves the search scripts, parameter files, negative search reports, intermediate coordinates, and old tables used during the research session. These files are historical evidence. They include weaker and abandoned candidates and are not all promoted results or Lean-verified statements.

The active finite certificates are indexed in `verification/certificate-index.json`. The research ledger explains the important branches and what has not been verified. Copied numerical inputs retain their source fields. Downloaded third-party manuscripts, images, PDFs, and vendor packages are referenced or hashed in `evidence/omitted-local-assets.json`, rather than bundled here.

Many historical scripts expect the original `work/kobon/` and `outputs/kobon-*/` layout. To reconstruct it without changing the checked packages:

```sh
python scripts/restore_experiments.py --dest work/experiment-resume
```

This copies files and does not run searches. Work from that new directory for scripts using relative paths. Numerical exploration can require NumPy, SciPy, and mpmath; consult the imports of the chosen script. Exact verification in the active `research/` packages uses only the Python standard library. Search scripts may write new reports on invocation; preserve their seeds and stopping rules. Their original downloaded vendor directories and absolute machine paths are not dependencies of the Lean library.

Important file groups:

- `hybrid-*.search.json`, `local-*.search.json`: proposal/acceptance counts and explicit search limitations.
- `grid-report-*`, `positive-control-19.json`: grid-compatibility attempts and successful control.
- `relaxed-*`, `mutation-*`, `pencil-*`, `stable-seed-*`: intermediate seed families.
- `earlier-gap-two-*`: superseded 21-line family draft.
- `audit_fp_*`, `table_baseline*`, `bounds_table*`: comparison and domination checks.
- `fixed-cap-*`, `pu-*`, `far-*`, `doubled-*`: finite construction experiments, some still exploratory.

The index records what was copied and the original relative location. The root evidence manifest supplies integrity hashes.
