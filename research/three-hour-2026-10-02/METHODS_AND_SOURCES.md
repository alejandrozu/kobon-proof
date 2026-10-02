# Methods and source record for the 2 October research session

Authorized session window: 2 October 2026, 16:49:48–19:49:48 UTC. Starting repository
revision: `8d9f20a6c8afcc0312c5f28f81050cb8fa2595c0`.

## Starting point

The September release proves the all-order `Universal.baseline_sound`, actual
one-step BBL doubling, and finite coordinate certificates. It does not prove
that the output of doubling can be used recursively. The manuscript's
infinite-family arithmetic must not be confused with that missing geometric
invariant. The session first targeted this precise gap.

The retained universal baseline is
`G(n)=floor(n(n-3)/3)+1+(n mod 2)` for `n>=4`, with the stated small exceptions.
Its source and the existing 138 coordinate certificates are the comparison
baseline, not a claim that every retained finite value is a literature record.

## Connections to the author's other projects

The no-three-in-line research notes reduce a modular construction to small
symmetry orbits and exact symbolic cases. The transferable idea is to search
within a structured family and certify the complete parameter domain. A
modular determinant cap is not itself a real-line Kobon construction; no such
implication is used here.

The Erdős 196 construction uses an explicit invariant on a finite prefix and
its auxiliary tail. The transferable idea is to retain the information needed
for the next stage instead of recording only a successful output count. In
Kobon this becomes the sorted tangent grid, saturated distinguished line,
positive central apex, and a duplicate-free triangle witness. The analogy is
methodological; no Erdős theorem is imported as a Kobon lemma.

Local source notes inspected: the author's September no-three-in-line
structural note and the self-contained Erdős 196 construction proof. Their
own proof and priority qualifications remain unchanged.

## Recent primary sources inspected

1. Roman Parpalak and Denis Utkin, [Enumeration and Classification of
   Triangle-Maximal Pseudoline Arrangements](https://arxiv.org/abs/2607.29236v1),
   submitted 31 July 2026; inspected 2 October. Reduced-word enumeration and
   symmetry classes offer different candidate combinatorial types for seed
   fitting. Its large first-hit examples are **pseudoline** arrangements;
   straight-line realizability must be established separately.
2. Bogdan Georgiev, Javier Gómez-Serrano, Terence Tao and Adam Zsolt Wagner,
   [Mathematical exploration and discovery at scale](https://arxiv.org/abs/2511.02864v3),
   revised 22 December 2025; inspected 2 October. The useful method is to
   combine structured search, mathematical guidance and independently checked
   evaluation, then seek a general theorem. Their discussion of numerical
   evaluator failures motivates exact final certification here. No result in
   that paper is treated as a solution of Kobon.

The BBL construction itself remains attributed to Bartholdi, Blanc and
Loisel, using the already retained primary paper and literature audit. New
formalization is not a claim to have invented their doubling gain.

## Directions pursued

- Close coordinate retention, next-grid saturation, arbitrary label
  permutation, seed normalization, and finite-depth parameter choice.
- Preserve a visible-pair list under the same recursion to prove the stronger
  adjacent-even family, rather than infer it from finite checkpoints.
- Strengthen local cyclic-fan geometry, while keeping global segment
  extraction and charging hypotheses explicit.
- Search new combinatorial types for a perfect grid-compatible seed; such a
  seed could improve every subsequent dyadic level.
- Test exact deletion and singular/multiple-line insertion neighborhoods.
  A bounded search failure is not an impossibility or optimality theorem.

The final session report and saved logs distinguish completed Lean theorems,
native-evaluation dependencies, exact computations, and unresolved directions.
