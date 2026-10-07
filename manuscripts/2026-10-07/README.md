# Kobon manuscripts: comprehensive and journal editions

**Alejandro Zarzuelo Urdiales — 7 October 2026**

These editions incorporate the March–September results, the October 2 work,
and the completed October 5–6 research. Earlier sources and PDFs remain in
[`paper/`](../../paper/README.md) and
[`manuscripts/2026-10-03/`](../2026-10-03/README.md).

- [Comprehensive edition](long/Kobon_comprehensive_2026-10-07.pdf): detailed
  proofs, source comparison, all 138 finite coordinate identities, the 3–60
  inventory, scientific figures, exact experiments and remaining research.
- [Journal edition](journal/Kobon_journal_2026-10-07.pdf): a concise article
  with readable proofs, attribution, references and clickable theorem roots.
  The supplied 11-point, 25 mm-margin layout is limited to 15 pages including
  references; the actual page count is recorded in its compilation report.
- [Portable LaTeX source package](Kobon_manuscripts_2026-10-07_sources.zip):
  both editions, their bibliography, vector figures, tables and build helper.
- [Full proof map](shared/proof_map.md),
  [machine-readable map](shared/proof_map.json),
  [coverage map](shared/coverage_map.md), and
  [old/new contribution comparison](shared/contribution_comparison.md).
- [Primary-source and novelty audit](shared/literature_scope_audit.md).

The final publication files use the repository tag `manuscripts-2026-10-07`.
Mathematical theorem links use the separate frozen Lean-source revision below.

## Principal changes

The actual deficit-dependent successor now applies to every supplied simple
seed with n≥3. Its exact gain is
`min(floor(n/2), ceil(max(3,max(0,n-delta))/2))`, and it can be iterated
indefinitely through both parities. Actual terminal rays and integer averaging
discharge the former visibility/charging gap. The gain depends on the seed;
the theorem does not assert a full half-order gain from every input.

Poola's 61-line, 1190-triangle point arrangement has an independently refitted
compatible actual-tangent seed. The strongest seed has 29 visible pairs.
For `q=60*2^t`, the resulting simple families give `1200*4^t-10` triangles
at `q+1` lines and `1200*4^t+30*2^t-11` at `q+2`. The even family is one
above the preserved 28-pair family at every depth. Poola retains the original
point-count credit; BBL retains the doubling construction. The allowable
positive parameter interval may shrink at each depth.

Canonical actual fans, shared-side matching, marked ports, graph components
and finite geometric escape now supply degree-free structural upper bounds.
The strongest global all-triple estimate retains the positive M22 term;
the strongest component portfolio retains N12 and does not contain M22.
The actual corrections and class hypotheses remain visible. No new
unrestricted numerical upper formula for K(n) is claimed.

The known 33/37/49 numerical orbits now have complete compatible seed and
recursion proofs, and the executable all-order maximum retains the previous
envelope pointwise. Exact triangle germs supply a general birth/loss calculus.
Four- and six-line real-interval examples expose the precisely stated
half-plane loss error and the possibility of three old-triangle losses.
The concrete 41-line dual is external computation, and the remaining
zero-component equality decomposition is mathematical analysis.

Every distinct earlier contribution remains represented: the March-associated
28:238, 30:275 and 34:357 witnesses; phase/affine improvements; the visible-list
extension and its resource limitation; the ten-dyadic families; finite inputs;
simple upper bounds; shared-fan and smoothing diagnostics; and earlier
obstructions/searches. The map retains all 89 historical and all 160 October 3
claim IDs plus all 138 coordinate identities, including 104 simple identities.
The current map has 200 scoped entries, comprising the 160 retained entries
and 40 additions; these are coverage entries, not a discovery count.
Recursive existence bounds do not inflate the finite-coordinate catalog.

## Mathematical revision and verification

Lean links are pinned to
[`f44f23ee062a255f5cad7d39188fd55c0feb83a8`](https://github.com/alejandrozu/kobon-proof/tree/f44f23ee062a255f5cad7d39188fd55c0feb83a8).
The completed local replay covers 638 active modules and audits 9,058 theorem
declarations: 8,046 use standard axioms only and 1,012 additionally descend
from explicit finite native-evaluation roots. Its evidence is frozen at
[`af74635d8b25b32703088460bc41854bb18e1a05`](https://github.com/alejandrozu/kobon-proof/blob/af74635d8b25b32703088460bc41854bb18e1a05/verification/lean-summary.json).
The shared JSON records any confirmed clean CI run by its own commit;
the historical successful run is not attributed to the new mathematical pin.

The incremental local replay records 265 directly compiled modules and reuses
373 unchanged source/import closures from the hash-pinned verified baseline,
and reruns the complete root axiom audit. It is distinguished from a clean
CI rebuild of the complete library. Consult
[release verification](RELEASE_VERIFICATION.md) and
[proof-map validation](shared/proof_map_validation.json) for final status;
a hash/label check alone does not establish a successful Lean rebuild.

Structural and analytic proofs use only `propext`, `Classical.choice`, and
`Quot.sound`. Executed finite seed checks additionally depend on explicit
native-evaluation roots. The seed-61 odd/even branches inherit five/seven such
roots. Conditional interfaces prove their implications; ordinary arguments,
external exact computations and unfinished branches retain separate labels.
Audit counts describe the retained implementation, not mathematical discovery
counts or publication priority.

## Compile the portable source package

Extract the ZIP, install Tectonic and Python with `pypdf`, and run from the
directory containing `build.py`:

```sh
python build.py --edition both
```

Use `--engine /path/to/tectonic` to choose an executable, or `--edition journal`
for the short paper. Each edition has `main.tex`, section sources, a
bibliography and vector figures; the long edition also has generated tables.
Current TeX Live can compile either edition with
`latexmk -pdf -outdir=build main.tex` from its directory. Tectonic may fetch
standard packages on its first run. Source-map reconstruction and Lean replay
need the full repository; typesetting the portable archive does not.

## Reproduce the source and PDF checks

From a complete repository checkout:

```sh
python manuscripts/2026-10-07/shared/build_proof_map.py
python manuscripts/2026-10-07/shared/validate_proof_map.py
python manuscripts/2026-10-07/validate.py
python scripts/evidence_manifest.py --check
```

The shared validator checks all preserved identities, immutable source hashes,
declaration lines and numbered labels. The release validator records fonts,
references, page limits, links, historical preservation and visual-review
records. A rebuilt PDF may have different bytes; render and review those bytes
before recording a new visual review.

`render.py` uses `pypdf`, Pillow and Poppler's `pdftoppm`. Figure formulas,
parameter choices and source hashes are recorded in the generated manifests.
The older figures retain their generation evidence. Cropped seed illustrations
are explicitly windows of the construction, not a simultaneous display of
every triangle.

Full Lean/exact replay commands remain in the
[repository README](../../README.md) and
[October 5–6 research record](../../research/openmath-seven-hour-2026-10-05/README.md).
The journal's 15-page limit applies to the supplied layout; another class can
change pagination.
