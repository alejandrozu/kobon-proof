# Suggested claim and attribution

Prepared for Alejandro Zarzuelo Urdiales · 20 September 2026

The defensible claim is a quantitative extension theorem valid for both parities, together with the full odd-to-even gain under a saturation hypothesis. The blanket recurrence with gain $\lfloor n/2\rfloor$ is still a stronger, unproved statement here.

## Suggested contribution paragraph

> Starting from Zarzuelo's odd-to-even extension proposal, we give a quantitative one-line extension theorem for simple affine line arrangements of arbitrary order. The number of additional triangles is controlled by the unused-segment defect through an explicit boundary count. In particular, every arrangement of $2m+1$ lines with at most two unused bounded segments admits an extension preserving all existing triangles and creating exactly $m$ new ones. A finite boundary criterion and a weaker unconditional estimate cover both parity transitions. The cyclic counting core and selected rational examples are formally checked in Lean.

## The mathematical claim

If $A$ is a simple arrangement of $n\ge3$ lines with $T$ triangles and
$d=n(n-2)-3T$, the construction supplies

\[
t(A\cup\{L\})\ge
T+\left\lceil\frac{n-1}{2n}\max\{3,n-d\}\right\rceil.
\]

This statement has no parity restriction. When $n=2m+1$ and $d\le2$, it recovers $T+m$. In particular, it applies to every simple odd arrangement attaining $\lfloor n(n-2)/3\rfloor$.

## How to describe novelty

The potentially distinctive contribution is the explicit defect-dependent estimate, the finite criterion for the full gain, and the precise scope of the defect-two corollary. Priority for those formulations is not established by the present search. They may overlap with consequences implicit in earlier work.

Exterior addition itself is prior art. Bartholdi–Blanc–Loisel discuss it for perfect odd arrangements, and Blanc uses distant-line additions for several even examples. Blanc also develops unused-segment charging arguments. These should be acknowledged near the contribution paragraph, not only in a bibliography. [BBL, Introduction](https://arxiv.org/html/0706.0723v1); [Blanc, Sections 2 and 5](https://arxiv.org/html/0801.2845v2).

The infinite family at orders $18\cdot2^t+2$ in the manuscript is an attributed corollary of the Parpalak–Utkin odd family and the extension argument. Its seed and iterative construction belong to the earlier authors. Its priority and any record status are not claimed here. [Parpalak–Utkin](https://arxiv.org/abs/2604.22035).

## Provenance and formalization

The March 2026 Archivara paper records the original proposed universal odd-to-even principle. This September draft supplies a different counting proof with explicit hypotheses and a weaker unconditional rule for both parities. Keeping those dates and statements distinct gives a more accurate attribution record. [Original paper](https://archivara.org/paper/48b411c9-0e03-4592-931e-179b9a1c2312).

The supported formalization wording is:

> The finite cyclic counting argument and selected exact rational examples have been checked in Lean without placeholder proofs. The geometric reduction from arbitrary Euclidean arrangements to the finite boundary data is supplied as a mathematical proof and remains to be formalized in Lean.

“The universal recurrence is completely machine verified” would not describe the delivered result.
