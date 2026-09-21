# Reproduction tools

Run from the repository root, with Python 3.10+ and the pinned Lean toolchain.

| Command | Purpose |
|---|---|
| `python scripts/verify_lean.py --jobs 2` | Build all active results and reject unapproved proof dependencies; write full logs and source hashes. |
| `python scripts/verify_coordinates.py` | Independently count every distinct promoted arrangement by two exact methods and check simplicity. |
| `python scripts/verify_seed_interval.py` | Reproduce the rational interval argument in a scratch directory and compare it to the saved evidence; this is not a Lean proof. |
| `python scripts/generate_all_n.py` | Generate the all-order envelope, explicit exceptions and theorem references from the finite certificate index; Lean proves the baseline geometry independently. |
| `python scripts/generate_seed_family.py` | Reproduce rational parameter-box data for the real trigonometric seed. Lean independently checks the generated data and real theorem. |
| `python scripts/audit_successor_chain.py` | Reproduce the exact 49-line exterior chain, save every coordinate/profile, and regenerate kernel-checked finite profile theorems. |
| `python scripts/evidence_manifest.py --check` | Check the stable evidence files against their recorded hashes. |
| `python scripts/restore_experiments.py --dest work/experiment-resume` | Recreate historical search paths without modifying the promoted packages. |

To deliberately regenerate the coordinate table and Lean data after a research change:

```sh
python scripts/materialize_table.py
python scripts/generate_lean_certificates.py
python scripts/prepare_verification.py
python scripts/generate_all_n.py
python scripts/verify_lean.py --jobs 2
python scripts/verify_coordinates.py
python scripts/verify_seed_interval.py
```

Then review the index, result documentation, theorem scope, and attribution before refreshing the evidence manifest with `python scripts/evidence_manifest.py`. A changed manifest is an intentional revision of the evidence, not a verification of a mathematical claim. Build summaries hash their own checked Lean sources. A full regeneration replaces the index; partial generation is intentionally disabled to prevent accidentally dropping claims.

The generators use exact arithmetic to propose data. Their correctness is not assumed in `validate_sound`: each coordinate and supporting triangle is checked by the Lean certificate. Native evaluation's trust boundary is documented in `FORMALIZATION.md`. The coordinate lists are committed so building the Lean development does not require rerunning any numerical search.
