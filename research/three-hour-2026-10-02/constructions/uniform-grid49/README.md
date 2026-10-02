# Uniform 49-line seed: exact certificate

An explicit fixed rational reciprocal-slope vector gives **767 triangular
cells on 49 lines for every 0 < ε ≤ 1/100**. The distinguished line has all
47 consecutive segments capped by triangles, its central apex is positive,
and 24 exterior pairs are visible in the common direction (1,−2).

The complete data are in `uniform-seed.json`; `verification.json` and
`visibility.json` record the two exact audits. These are computer-assisted
certificates. The separate Lean modules and their build status are recorded
by the session's formalization report; this directory does not infer that
an uncompleted Lean build has passed.

## Construction

Let Y₀ be y = 0. The other 48 lines, in their order of intersection with Y₀,
are Lᵢ: x − vᵢy = aᵢ(ε), for 0 ≤ i < 48, with

\[
a(\varepsilon)=
(-\tan(23\pi/48),\ldots,-\tan(\pi/48),-\varepsilon,
 \varepsilon,\tan(\pi/48),\ldots,\tan(23\pi/48)).
\]

The 48 rational values vᵢ appear in the JSON field `reciprocal_slopes`.
They are fixed, positive, pairwise distinct, and have denominator dividing
10¹⁰. The file labels Y₀ as line 0 and Lᵢ as line i+1. Thus the central
triangle is (0,24,25). Its height is 2ε/(v₂₃−v₂₄) > 0.

The 23 tangent constants are enclosed by outward rational intervals, using
Machin's identity for π and Taylor remainder bounds for sine and cosine.
The independent calculation uses only Python integers and fractions. The
smallest certified absolute old-support determinant at ε = 0 exceeds
8.37 × 10⁻⁶. All 17,296 old-support triple signs remain strict throughout
0 ≤ ε ≤ 1/100. The 1,128 pair-normal determinants are fixed and nonzero.
Since 1/100 < tan(π/48), every crossing on Y₀ is strictly ordered for positive
epsilon, including the central pair −ε < ε.

Every determinant sign of the affine arrangement therefore stays fixed on
0 < ε ≤ 1/100. The rational midpoint at ε = 1/200 is counted by two distinct
exact algorithms: vertex adjacency and direct oriented signs. Both count
767 bounded triangular cells, including all 47 distinguished caps. The
cell predicate is a finite Boolean combination of these determinant signs,
so the same triangle list applies throughout the parameter interval.

## Uniform exterior data

For w = (1,−2), `visibility.json` lists 24 pairs and checks the exact
`Kobon.Exterior.VisiblePair` sign conditions. Every directional determinant
is a nonzero constant. Each evaluation numerator is affine in epsilon;
2,256 rational interval checks at the two endpoints certify its required
weak sign on the whole interval. The rightmost pair (0,48,49) is included.
The last reciprocal slope is 3, so the corresponding ordinary slope is 1/3
and w₁ + w₂/3 = 1/3 > 0. Direction (1,0) supplies only 22 pairs and is not
the direction used by this certificate.

## Relation to the recursive construction and attribution

These data supply the geometric seed interface for the separately proved
BBL recursion. With q = 48·2ᵗ, its odd and adjacent even counts are

\[
T_{q+1}=768\,4^t-1,
\qquad
T_{q+2}=768\,4^t+24\,2^t-1.
\]

The odd numerical values are explicitly classical: Theorem 1.3 of Bartholdi,
Blanc and Loisel, [On simple arrangements of lines and pseudo-lines in
P² and R² with the maximum number of triangles](https://arxiv.org/abs/0706.0723)
(2007 preprint; 2008 publication), gives the optimal family n = 6·2ˢ+1.
Our odd orders are its tail s = t+3. No new finite record or priority claim
is made. The contribution of this
experiment is an explicit uniformly compatible parameter family, exact
reproducible certificates, and the opportunity to connect a 49-line seed to
the repository's formal recursive invariant. The source affine type is the
attributed retained witness `research/finite-table/simple-049.json`.

The floating discovery first fits that original affine type by preserving
both old-support triple signs and signs involving the original line at
infinity. Preserving only the projective signs produced a 743-cell example,
despite its 47 distinguished caps; that example was not a perfect seed.
The affine screen checked all 49 distinguished supports at four positive
epsilon values and found 100 exact rational midpoint fits. At epsilon zero,
25 supports gave strictly feasible old-support/pair systems. Support 27 was
chosen for its positive margin, then its reciprocal slopes were rounded
once and all subsequent claims were verified with exact arithmetic.

## Reproduction

From the repository root, using standard Python:

```text
python -B experiments/2026-10-02/verify_uniform_grid49.py \
  research/three-hour-2026-10-02/constructions/affine-grid49-limit/n049-I27-limit-slopes.json \
  --out research/three-hour-2026-10-02/constructions/uniform-grid49

python -B experiments/2026-10-02/verify_uniform_grid49_visibility.py \
  research/three-hour-2026-10-02/constructions/uniform-grid49/uniform-seed.json \
  --out research/three-hour-2026-10-02/constructions/uniform-grid49/visibility.json
```

Both validators were independently inspected during this session. The local
Y₀-order premise is explicitly asserted in each. Floating LP software is
needed only to rerun `affine_grid_fit.py`, not either exact validator.

`lean-export-audit.json` additionally records an independent parse of the
actual generated `BBLSeed49.lean` and `BBLSeed49Exterior.lean` source data.
It verifies equality with this family, containment of the separately proved
tangent bounds in the exported 30-decimal boxes, 1,176 direction checks,
18,424 simplicity checks, 37,583 triangle/support checks, and 1,176 visible
pair/support checks using the exact `Parametric` predicate semantics. This
checks the finite predicates but does not assert that a pending Lean build
has completed. The audit can be replayed without modifying frozen evidence:

```text
python -B experiments/2026-10-02/audit_lean_grid49_export.py \
  --out verification/research-2026-10-02/lean-export49.json
```

Optional `--seed-source` and `--exterior-source` paths select explicit source
files. By default the auditor uses the active modules, or an unambiguous
archived source with the same filename under the session's research directory.
