# Structural seed probes

The numerical goal is to improve a uniform61-line saturated-axis seed beyond
1190 cells, thereby reducing the constant deficit of an entire dyadic family.
An isolated31-line count below its known299 optimum is not a new record;
it is relevant only if it supplies a stronger compatible recursive seed.

## Evidence and current boundaries

The starting1190 whole-interval seed belongs to the construction branch.
`verify_uniform61_candidate.py` independently replays it in a reciprocal
normal chart. All35,990 simplicity and72,590 triangle/support interval checks
pass for `0<epsilon<=10^-8`, using the compiled actual tangent60 bounds.
This is an exact external replay, not another concrete Lean proof.

The chamber search scores actual triangle mutations before attempting a
strict-sign LP. Adjacent normal directions may also swap across a parallel
facet, changing the affine chart while all retained proposals remain
pairwise nonparallel. The source triangle mutation is a search operation,
not a proved general construction. Capped lower-score states are used only
as temporary paths; they are not advertised as progress.

With ordered tangent intercepts, emptiness of each adjacent-axis cap is
linear in reciprocal slopes after the adjacent direction sign is fixed.
Simple adjacent caps alternate sides of the axis. The cap cone therefore
permits a larger search than preserving every original orientation sign.
Exhaustive one-coordinate chamber sweeps and finite-temperature moves are
screening tools; all-n or global optimality does not follow from them.

## Optimal31 projective recharting

The repository already contains the exact published input
`research/finite-table/classical-031.json`:299 cells and465 distinct ordinary
crossings, with29 saturated lines in its original affine chart. This point
input is prior research. All29 original-infinity axis fits produced no
positive floating margin; these are diagnostics, not infeasibility proofs.

Changing the line at infinity can lose bounded triangles. Every new chart
is recounted exactly and its actual saturated axes recomputed before fitting
the tangent grid. Counts297 and298 are still useful targets, since a
compatible uniform predecessor would give1197 or1198 at61 after a classical
doubling and hence improve the current constant9 deficit.

The full chart/fitting record is in `optimal31-projective-charts/report.json`.
No optimal31 uniform tangent-grid seed is claimed without a successful
exact whole-interval certificate.

## Forge direction criterion

[Forge--Ramírez Alfonsín (1998)](https://www.researchgate.net/publication/225741288_Straight_line_arrangements_in_the_real_projective_plane)
uses a regular star of directions, two special lines near a missing axis,
and an empty-special-cone condition. The original straight-line theorem
also assumes projective triangle maximality. At32 projective lines the
quantity32*31/3 is nonintegral, so that exact original hypothesis cannot be
silently applied to an optimal affine31-line input. A non-perfect extension
would require its own quantitative and geometric proof.

A projective map using an ordinary regular direction as the new infinity
relates the direction criterion to tangent-intercept normalization. This
relation does not preserve bounded counts automatically; it motivates the
explicit recharting/recount above rather than bypassing it.

Primary gallery metadata was inspected at
[`zegalur/line-order`](https://github.com/zegalur/line-order/tree/2631b8793eb351be2ad6b8a91b7194eeb67e25bb),
including the31/299 table attributed to Kyle Wood. Its display is optically
distorted, so screen coordinates were not substituted for line equations.
The existing exact repository input was used instead. Unmodified downloaded
code/display snapshots remain only in ignored `work/seed_search/line-order-primary`;
the uploaded research records contain source links, hashes and mathematical
data rather than republishing those display/code files.

## Infinitesimal-resolution graph probe

For the phase-zero Füredi--Palásti arrangement, a generic local triple
resolution selects one alternating sector class. Old triangles requiring
opposite choices at a shared triple conflict. The resulting finite
bipartite graphs have a perfect matching in56 tested orders8--60,99,120,195.
Even allowing independently selected resolutions, only half the old
triangles can survive in those tests. Adding one tiny triangle per triple
gives at most the currentG baseline for even orders andG-1 for odd orders.
`fp-resolution-matching.json` records the matching counts.

This is a finite combinatorial screen with an explained geometric model;
it is not a Lean all-order obstruction theorem, nor a statement about
arbitrary large perturbations. It is evidence to avoid spending substantial
time on small harmonic/offset perturbations of the same old family.
