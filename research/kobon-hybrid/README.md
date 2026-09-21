# Kobon hybrid-construction results

The verified eleven-line seed and published BBL doubling theorem prove

\[
K(10\cdot2^t+1)\ge\frac{100\cdot4^t-4}{3}
=\frac{(10\cdot2^t+1)(10\cdot2^t-1)}3-1,\qquad t\ge0.
\]

Every arrangement here is simple. The odd family stays one triangle below the classical upper bound. Our boundary-defect extension proves an adjacent even family two below the polynomial upper bound for simple arrangements. Explicit even witnesses through 162 lines improve that guarantee by one triangle.

Read [the manuscript](manuscript.md) for the proof, ten rational coefficients, attribution, comparisons, and limits on novelty claims. The eleven-line count and doubling theorem are prior work. Priority for the compatible realization and resulting family has not been established.

## Reproduce the checks

Use Python 3.10 or later, from this directory. No external packages are required.

    python verify_seed.py
    python generate_family.py 4

The first command proves stability over an entire parameter interval using rational arithmetic, then checks the reference arrangement with two independent counters. The second generates and verifies ten rational finite examples. A default run also uses four doublings. Large certificates have large rational coordinates and take longer than the seed check.

To check saved coordinates directly:

    python verify_direct.py certificates/n081.json certificates/n082.json certificates/n161.json certificates/n162.json

The infinite theorem follows from the interval-certified seed and BBL, not from finite sampling. None of these scripts is represented as a Lean proof.

## Delivered finite witnesses

| Odd lines | Triangles | Adjacent even lines | Triangles |
|---:|---:|---:|---:|
| 11 | 32 | 12 | 37 |
| 21 | 132 | 22 | 142 |
| 41 | 532 | 42 | 552 |
| 81 | **2132** | 82 | **2172** |
| 161 | **8532** | 162 | **8612** |

The first three rows are checkpoints, not claimed new numerical records. Known 21- and 41-line arrangements and our earlier 22- and 42-line bounds remain stronger at those orders.

**seed-verification.json** records 240 rigorous endpoint determinant checks. **seed-combinatorics.json** contains crossing orders and the 32 triangles. **finite-verification.json** records agreement of both counters, simplicity, and exterior gains. **manifest.json** supplies hashes for every delivered package file except itself.

## Research coverage

- Tried 1,274,096 candidate insertions through pairs of old finite vertices on selected 38-, 43-, and 50-line configurations. Numerical ranking was followed by exact verification of possible improvements; none improved the retained bounds.
- Evaluated 5,867,928 local one-line proposals in bounded searches at 39, 47, and 51 lines. Accepted changes were counted exactly; those searches found no higher retained bound.
- Tested published seeds on the tangent grid; a positive control reproduced the known 19-to-37 doubling.
- Obtained an intermediate compatible 21-line seed with 131 triangles, giving a two-triangle-gap family.
- Reworked the Honma/Savchuk eleven-line configuration to obtain the stronger final family and certified its complete small-parameter interval.

The negative searches are bounded heuristic experiments, not impossibility proofs. The final theorem can be checked from the coefficient vector and scripts without repeating the search.

