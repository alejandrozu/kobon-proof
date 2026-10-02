# Exact obstruction for a perfect 21-line tangent-grid seed

The complete affine-input audit **passed**. The independent standard-library
checker verified 3,765 polynomial positive dependencies and their 15,060
reflected/reoriented versions. These cover all 236 supplied Euclidean classes
and all 21 choices of distinguished support: **4,956 normalizations, no missing
cases**. The common certified interval is **0 < ε < 1/2,000,000**.

This is a construction-specific, computer-assisted obstruction. Completeness
of the published 236-class enumeration is an attributed external input. The
full dataset and coverage argument are **not** a Lean classification theorem.
A particular ten-sign obstruction has separately been proved in Lean for
every real epsilon, using only the standard axioms.

## Exact statement and its limits

Set t = tan(π/20), and prescribe the 20 ordered intercepts

\[
a(\varepsilon)=
(-\tan(9\pi/20),\ldots,-\tan(\pi/20),-\varepsilon,
 \varepsilon,\tan(\pi/20),\ldots,\tan(9\pi/20)).
\]

Take Y₀: y = 0 and Lᵢ: x − vᵢy = aᵢ(ε), for 0 ≤ i < 20. The audit excludes
a simple arrangement of this form with 133 bounded triangular cells and a
saturated distinguished line, throughout the interval above. The reciprocal
slopes may depend arbitrarily on epsilon, may diverge as epsilon tends to zero,
and need not converge. Translation and positive scaling of the entire grid
are removed by an affine coordinate change.

This is **not** an upper bound K(21) ≤ 132. Known optimal 21-line arrangements
with 133 cells remain valid. The result identifies a limitation of this
particular recursive tangent-grid ansatz. It does not exclude another grid,
another recursive invariant, or moderate epsilon. Priority of this observation
has not been established.

## Classification input and the corrected scope

The input is `../primary-inputs/data/exhaustive/21.uniq-e.txt`, published by
Roman Parpalak and Denis Utkin with their
[2026 classification paper](https://arxiv.org/abs/2607.29236). Its SHA-256 is
`288b070ecc0b9e8edf90b476cb2ae5a149d90d299cc74f451a6731414ca3f341`.
The pinned source commit and per-file URLs are in
`../primary-inputs/manifest.json`; licensing and attribution are documented
in `../primary-inputs/README.md`.

The source distinguishes 18 projective classes of the **22-support closures
including infinity** from 236 Euclidean classes of affine 21-support
arrangements. An earlier audit of only the 18 supplied representatives did
not establish complete affine coverage. That narrower audit is retained in
`exact/verification.json`: 366 systems and 0 < ε < 1/25000. The final result
uses the 236 Euclidean-class file, not an inference that the 18 representatives
alone suffice.

The final checker independently decodes every reduced word, checks its 210
crossings and 133 triangular cells, and normalizes each of its 21 supports as
the distinguished line. Global sign reversal and reflection of the symmetric
grid are handled explicitly. The Euclidean classes already fix the affine
infinity choice, so no extra projective-closure coverage is assumed.
Completeness of the external enumeration itself is not rerun.

## Homogeneous inequalities and certificates

For a sorted old-support triple i < j < k, its prescribed strict orientation is

\[
s\big((a_j-a_k)v_i+(a_k-a_i)v_j+(a_i-a_j)v_k\big)>0.
\]

For an adjacent pair i, i+1, saturation of the distinguished segment requires
σᵢ(vᵢ − vᵢ₊₁) > 0. Each remaining support forces the sign: for k < i it is
the sign of (k,i,i+1); for k > i+1 it is the negative of the sign of (i,i+1,k).
Disagreement is an exact combinatorial rejection, not LP infeasibility.

The coefficients lie in Q(t)[ε], with

\[
t^4-4t^3-14t^2-4t+1=0,\qquad 3/20<t<17/100.
\]

The actual tangent is the unique root in that interval. All other tangents
are reconstructed by T₀ = 0 and Tₖ₊₁ = (Tₖ+t)/(1−tTₖ). For each covered
system A(ε)v > 0, a nonzero polynomial vector satisfies

\[
w_i(\varepsilon)\ge0,
\qquad \sum_i w_i(\varepsilon)A_i(\varepsilon)=0.
\]

A strict feasible vector would imply 0 = Σᵢ wᵢ(Aᵢv) > 0. This pointwise
contradiction includes arbitrary epsilon-dependent slope choices. Bounds on
the slopes are used only for floating discovery, not in the final proof.

For each nonzero weight, the checker factors out its lowest power of epsilon.
The remaining leading algebraic coefficient has a strictly positive rational
lower bound. If the higher coefficients have total absolute upper bound M,
epsilon at most half the leading lower bound divided by M preserves positivity.
The smallest derived radius is approximately 6.9963259534 × 10⁻⁷, larger than
1/2,000,000. Every weighted-column identity is checked exactly modulo the quartic.

## Final artifacts and trust levels

* `affine-exact/certificates.json`: 3,763 exact support certificates.
* `affine-exact/coverage-repairs.json`: two additional certificates needed
  after replacing numerical supports by ones positive near zero.
* `affine-verification.json`: final complete independent check, including
  hashes, every coverage match, and the common radius.
* `affine-shared/supports.json`: floating discovery metadata only; 4,776
  systems were distinct after the recorded normalizing symmetries.
* `representative-238.json`: the compact ten-sign certificate used by the
  separate Lean proof. Its rows avoid both epsilon-dependent intercepts.

`Kobon.StrictLinearCertificate` proves generic positive-dependency soundness.
`Kobon.BBLTangentAlgebra` proves actual tangent identities and root isolation.
`Kobon.BBLGridObstruction.actual_grid_orientation_impossible` proves the
explicit representative for arbitrary real epsilon and reciprocal slopes.
The larger 3,765-certificate coverage remains computer-assisted rather than
an imported Lean theorem. The session's `bbl/LOCAL_ROBUSTNESS.md` separately
certifies robustness of that representative under independent perturbations
of its 11 used intercepts by at most 1/1000; this quantitative check is not Lean.

Exact geometric controls compare normalization with actual rational projective
transformations: the nine-line control checks 72 charts, 4,032 triple signs and
504 cap/cell comparisons; the 21-line control checks 420 charts, 478,800 triple
signs and 7,980 cap/cell comparisons. They support the implementation but do not
replace the classification assumption.

## Reproduction

Run from the repository root with standard Python. Scientific packages are
unnecessary for the final verifier:

```text
python -B experiments/2026-10-02/verify_affine_grid_obstruction.py \
  research/three-hour-2026-10-02/constructions/primary-inputs/data/exhaustive/21.uniq-e.txt \
  research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-exact/certificates.json \
  research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-exact/coverage-repairs.json \
  --out research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-verification.json
```

Discovery uses `cover_affine_obstruction.py`; symbolic production uses
`exact_grid_obstruction.py`, optionally accelerated by python-flint through
SymPy. `repair_affine_obstruction.py` replaces unsuitable supports, and
`merge_affine_certificates.py` joins worker ranges. The final verifier does not
import those producers, SymPy, NumPy, SciPy, FLINT, or an optimizer.
