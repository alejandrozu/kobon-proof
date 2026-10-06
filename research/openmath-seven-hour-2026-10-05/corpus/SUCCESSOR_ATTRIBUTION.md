# Successor construction: prior scope and current target

Primary-source check completed 6 October 2026 during the seven-hour session.
This note prevents a standard perfect-arrangement successor from being claimed
as new. It does not establish exhaustive historical priority for a broader
statement.

## Pinned primary evidence

**Bartholdi, Blanc and Loisel (2007), arXiv:0706.0723v1**, introduction,
paragraph following Theorem1.1:
[versioned full text](https://arxiv.org/html/0706.0723v1).
The web text locator is line58 (the substantive paragraph itself is the stable
locator if the renderer changes). Their stated operation starts by
“adding one line to an affine perfect arrangement” of odd order `n-1`
congruent to3 or5 modulo6. It obtains the even-order lower polynomial

```
n*(n-5/2)/3 = n*(2*n-5)/6.
```

The equivalence to the familiar successor gain is a direct arithmetic
calculation: the perfect odd count is `(n-1)*(n-3)/3`, and subtracting it
from that even polynomial gives `(n-2)/2`. Therefore, the perfect case
`K(n)>=K(n-1)+(n-2)/2` is established prior research.

**Pavlo Savchuk (2025), arXiv:2507.07951v1**, AppendixC.2,
[versioned full text](https://arxiv.org/html/2507.07951v1).
The web text locators are lines565–568. The24-line example is obtained by
an exterior addition to the23-line arrangement, following Bader's16-line
and Wood's20-line examples. The author also describes corresponding
21→22 and27→28 constructions and supplies the implementation entry
`lineorder.add_1_2_line`. These are explicit precedents for the individual
successor cases, including the27→28 numerical result.

**Jérémy Blanc (2008), arXiv:0801.2845v1**, Proposition5.0.1 proof and
Figure7, [versioned full text](https://arxiv.org/html/0801.2845v1).
The web text locators are lines253–254. Distant-line addition produces the
displayed even-order examples from the displayed odd inputs, including
7→8 and19→20. Both odd inputs have deficit two. Thus specific near-perfect
successor examples are also prior research. The general Lemma4.0.1 is a
pseudoline doubling result, rather than an arbitrary straight-source
one-line successor guarantee. No theorem guaranteeing the half-step from
every deficit-two straight arrangement was located in this version.

## What our current formalization should actually claim

Let a simple finite certificate have `n` lines, `T` bounded triangles, and
the integer deficit `delta=n*(n-2)-3*T`. The new target is an actual global
endpoint count `B>=n-delta`, together with finite projective-normal averaging
and the geometric exterior insertion. These ingredients give a quantitative
gain from the actual boundary resources of an arbitrary certificate.

In particular, for odd `n`, a certificate with `delta<=2` should guarantee
an exterior gain `(n-1)/2`. The `delta=0` specialization is the prior perfect
case above; the uniform `delta=2` scope and the general deficit-dependent
criterion are the broader research target. The present compiled root-order
arithmetic proves that `2*n` integer choices with total at least
`(n-1)*(n-2)` have a choice of size at least `(n-1)/2`. Actual geometric
extraction and the final successor theorem must be assessed from their own
completed Lean proofs, rather than inferred from this arithmetic lemma.

The original March individual28/30/34 numerical cases should not be presented
as a newly discovered perfect-case mechanism: their odd inputs27/29/33 all
have deficit zero. For example, `29*27-3*261=0`. Actual deficit-two examples
include31→32 (`31*29-3*299=2`) and49→50 (`49*47-3*767=2`). They illustrate
the broader uniform criterion if the actual boundary and insertion bridges
are completed; their previously published individual counts remain prior
research.

The relevant new standard-axiom helper modules are
`Kobon/OpenMathBoundarySampleExistence.lean` and
`Kobon/OpenMathBoundaryRootOrder.lean`. No new historical-priority claim
follows merely from their Lean verification. The root and construction
branches own the final endpoint extraction and geometric linkage.
