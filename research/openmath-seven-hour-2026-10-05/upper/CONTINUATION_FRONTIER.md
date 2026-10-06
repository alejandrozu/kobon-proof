# Upper-branch continuation frontier

The completed formulas and Lean roots are in `VERIFIED_PROGRESS.md`.
This file records additional proof targets, not completed theorems.

## The last double-recipient correction is now removed

The completed unrestricted all-triple double-recipient formula is

```
2*delta + B15 + J13 >= 2*U + 3*E3 + 2*P21.
```

The actual normalized five-sector chart proof is now complete in
`UpperOpenMathN13ActualNoDouble`. The final `UpperOpenMathN13Curvature`
wrapper derives the no-two-neighbor condition, proves `J13=0`, and yields
`2*delta+B15>=2*U+3*(E3+P21)` without source-count or component-size
restrictions. Partial-source recipient degree zero raises the `P21`
coefficient to three. `UpperOpenMathN13Degree` retains the transparent
conditional counting helper internally; the final arrangement theorem
does not assume its geometric condition.

The final completed `N12Recipient` geometry subsequently adds `+N12` to
this formula: a one-cap degree-two triple core cannot receive two
antipodal sources either. The unrestricted literal component portfolio in
`ClosedN12Curvature` retains the resulting rounded surplus.

## Restoring a positive component escape term

After removing double receivers, a source-free estimate still does not
automatically give `delta>=U+c`. The remaining flat recipients can include
nonfull zero-cap degree-four cores that receive two antipodal sources;
their local curvature two pays those two arrivals exactly. Full zero-cap
degree-six cores have zero local curvature. A finite support extremum
rules out exposed full fans, but this alone does not rule out an exposed
flat nonfull receiver. A proof must identify the actual continuation or
outside-ray slack at such a receiver, or show that its paid source cluster
is closed and forces an escaping point. Do not infer strict component
positivity from pointwise nonnegative discharging.

A more specific lemma completed at the final source freeze is that a `(1,3)` receiver
with one antipodal-source neighbor cannot be a core support extreme.
After normalizing its ordinary tip to ray three, the middle incoming
antipodal source is locally incompatible with the two adjacent core tips.
An endpoint source forces an actual opposite continuation on the first
radial support, yielding a core on the other side of the center. The
mirrored endpoint is analogous. This precise support-escape consequence
is now formalized, including actual chart and neighbour extraction, in
[N13ActualSupportExtreme](../../../Kobon/UpperOpenMathN13ActualSupportExtreme.lean).
Normalized `(2,2)` and poor `(0,2)` boundary configurations still require
attention. This completed escape does not by itself establish strict
positivity for every component.

## Extending marked discharging beyond triple cores

At multiplicity `r>=5`, the unadjusted weight
`W=2*r*(r-2)-2*d1-d2` satisfies `W>=2*d2` from `d1+d2<=2*r`.
At a quadruple core the shortfall is
`max(0,2*d1+3*d2-16)`. This suggests a mixed resource bucket in which
higher cores can absorb marked ports.

However, the current balanced-receiver exclusion and one-cap recipient
bound use all-core-triples hypotheses: their cap propagation can inspect a
third core. The actual arbitrary-multiplicity antipodal source cone is
available, but the triple-only exclusion cannot silently be reused in the
mixed argument. Prove a localized exclusion with its necessary neighboring
multiplicities displayed, or retain an explicit higher-core correction.

## The unrestricted numerical even bound remains open here

Two empirical token targets are `C>=2*D1` and, in the all-triple class,
`n<=2*U+D1+Rc+2`. The raw latter rule without `+2` has exact counterexamples;
the `+2` rule also fails once higher cores are allowed. Neither empirical
target is a consequence of the completed component formulas. Any progress
must reconcile ordinary-three-fan and kite blocks globally, with boundary
resources kept in the ledger.

## Further finite surplus terms

The current unit-discharge calculation appears to retain additional
point margins for `(d1,d2)=(0,0),(0,1),(0,3),(1,0),(1,1),(2,0)`, with
coefficients `6,3,1,4,1,2` respectively. These arithmetic refinements were
not promoted or formalized before the source freeze. In particular an
additional zero-cap degree-three term would need no new recipient
geometry beyond the completed bound of two antipodal neighbors. Keep
these proposed positive-profile refinements separate from the completed
`E3`, `P21`, and `N12` terms.
