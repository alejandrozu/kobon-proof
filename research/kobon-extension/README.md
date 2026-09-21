# Kobon extension: corrected statement, proof, and formal core

Prepared for Alejandro Zarzuelo Urdiales · 20 September 2026

Start with **manuscript.md** for the complete mathematical argument and **claim_and_attribution.md** for wording suitable for a revised paper.

The package establishes an explicit extension bound for simple arrangements of every order $n\ge3$. It recovers the full $+m$ odd-to-even gain whenever the input has at most two unused bounded segments. The stronger recurrence $K_s(n+1)\ge K_s(n)+\lfloor n/2\rfloor$ for every $n$ is **not proved here**.

## Contents and verification scope

- **manuscript.md:** definitions, geometric proof, both-parity bound, sharp odd corollary, iteration, attributed infinite-family corollary, and limitations.
- **claim_and_attribution.md:** suggested contribution language and the distinction between a contribution claim and an established priority claim.
- **BoundaryExtension.lean:** checked cyclic double-counting, averaging, defect consequences, parity statements, and the seven-line boundary-profile limitation.
- **RationalExamples.lean:** kernel-checked simple rational arrangements with triangle counts 3, 4, 5, 7, and 10.
- **certificates/:** eight rational arrangements; the 19-line seed is from Parpalak–Utkin.
- **boundary_extension.py:** exact exterior-line construction and boundary-profile computation.
- **exact_geometry.py / verify_direct.py:** independent triangle counters, using consecutive edges and same-side signs respectively.
- **verify_all.py / verification.json:** reproducible finite checks and results.
- **BoundaryExtension.log / RationalExamples.log:** successful compiler output and theorem axiom audits.

The general geometry in the manuscript has not been formalized end to end in Lean. The Lean counting theorems take explicit finite boundary data and numerical hypotheses; they contain no placeholder theorem asserting that all arrangements have the desired full gain.

Both counters agree on all eight certificates. Every arrangement is checked for distinct directions and absence of triple intersections. The chains $5\to6\to7$ and $19\to20\to21$ preserve every earlier triangle. The second chain has counts $107\to116\to126$ and is a demonstration, not a record claim. The deterministic 560-case regression checks the boundary inequalities, the cyclic mass identity, and the exact exterior gain.

## Reproduce the exact arithmetic checks

With Python 3, from this directory:

    python verify_all.py --regression

This uses only the Python standard library. It writes verification.json.

## Reproduce the Lean checks

The files were compiled with Lean **4.31.0** and Mathlib revision **fabf563a7c95a166b8d7b6efca11c8b4dc9d911f**. The local Mathlib checkout was clean. The supplied toolchain and Lake configuration pin those versions. With Lean/Elan/Lake available, the standard setup is:

    lake update
    lake exe cache get
    lake env lean BoundaryExtension.lean
    lake env lean RationalExamples.lean

The recorded run used an existing local Mathlib cache at that revision; a fresh network installation was not needed. The two compiler logs contain no errors or placeholder-proof axioms. Rational examples use kernel evaluation, not floating-point arithmetic or native compilation as a proof oracle.

## Attribution

The 19-line seed is the decimal dataset from [Parpalak–Utkin's repository](https://github.com/parpalak/triangle-maximal-18-series/blob/master/data/n19/lines.csv), interpreted here as exact rational coefficients and independently counted. The seed, the doubling constructions, and prior distant-line methods retain their original attribution.

No claim of a new best lower bound for every order, first discovery of exterior addition, or established priority for the quantitative formula is made. The earlier output folder kobon-research concerns a different derived family and is separate from this package.
