# Actual antipodal cone resources

These results concern an actual pairwise nonparallel straight-line arrangement
and an injectively indexed family of actual bounded triangular cells. Every
statement below is checked by Lean using the standard logical axioms; no
ordering, fan extraction, endpoint matching, or oracle for the geometry remains
as an extra hypothesis. Scope restrictions are listed explicitly.

At a core, let `a` count shared sides to ordinary vertices, `d` shared sides to
other cores, and `m` the marked rays with two ordinary shared neighbors. In the
all-triple class every core has exactly three supporting lines. Let `A0` be
the cores with `(a,d,m)=(2,4,0)`, whose ordinary rays are antipodal.

1. Two `A0` cores cannot share a side. The proof uses actual neighboring
   triangle occurrences to propagate support lines and derives a wrong-ray
   contradiction. See `UpperOpenMathAntipodalAdjacency.lean`.
2. An `A0` core cannot share a side with an unmarked `(2,2,0)` triple. The
   neighboring fan may have only five triangular sectors; the missing sector
   is not assumed present. See `UpperOpenMathAntipodalBalancedAdjacency.lean`.
3. The two outer core neighbors at either cap of an `A0` star cannot both be
   full triple fans. Thus an `A0` core has at least two neighbors that are
   nonfull triples or higher-multiplicity cores. This latter statement allows
   arbitrary multiplicities elsewhere. See
   `UpperOpenMathAntipodalFullNeighborPair.lean`.
4. In the all-triple class, those actual incidences give the bipartite resource
   inequality `2 * |A0| <= |E(A0,NonFull)|`. No independence of recipients is
   assumed. See `UpperOpenMathAntipodalConeIncidence.lean`.
5. At any multiplicity, a selected side from a fully shared core to another
   core is a shared core-to-core side. This is derived from actual canonical
   rays and the complete triangular fan. See `UpperOpenMathFullCoreSides.lean`.
6. In the all-triple class, a `(a,d)=(1,3)` core has a neighbor outside `A0`.
   Its three core rays contain an adjacent pair; their actual selected cap
   side would join two full `A0` cores if every neighbor lay in `A0`, contrary
   to item 1. No marked-count assumption is needed. See
   `UpperOpenMathOneCapThreeCore.lean`.
7. Two antipodal full triple cores with the same four actual core neighbors
   are the same center. Strict antipodal pairings of four points determine
   their unique diagonal intersection. This uniqueness allows other cores
   to have arbitrary multiplicity. See
   `UpperOpenMathAntipodalCenterUniqueness.lean` and
   `UpperOpenMathAntipodalSameNeighbors.lean`. It excludes the seven-vertex
   abstract half-charging sharpness graph as a real arrangement; that graph
   remains a valid example for the finite relaxation only.
8. More strongly, distinct antipodal full triple sources share at most two
   actual core neighbors. Any three outer corners put the center strictly
   inside one of their three boundary segments. Competing centers on the
   same segment are blocked by an intervening vertex; competing centers on
   different segments force strict interior crossing of selected cevians,
   impossible for elementary arrangement sides. See
   `UpperOpenMathCevianCrossing.lean`, `UpperOpenMathQuadThreeBoundary.lean`,
   and `UpperOpenMathAntipodalThreeNeighbors.lean`. All are kernel-checked
   with standard axioms. Only the two source centers need multiplicity three;
   common and other cores may be larger. The source/build hashes and printed
   axiom roots are in `VERIFICATION.json`.
9. In the all-triple class, **every** recipient with `a+d<=4` has at most
   two incident `A0` neighbors. This includes the zero-cap four-core type
   `(0,4)`, so its previous numerical degree-four capacity can be cut in half.
   The proof selects antipodal neighbors in the actual shared-ray run;
   three selected rays would contain an adjacent pair whose actual cap side
   contradicts anti--anti exclusion. The exact ray-to-edge bijection gives
   the recipient count. See
   `UpperOpenMathNonfullAntipodalRecipients.lean`.
10. The final N13 geometry excludes two `A0` neighbors at a `(1,3)` core.
    The antipodal, separated-core, and separated-ordinary cases are all
    checked, including actual shared-endpoint identification and finite
    source-chart classification. `UpperOpenMathN13Curvature.lean` derives
    the actual degree bound and eliminates the earlier `J13` correction.
11. A `(1,2)` core also has at most one `A0` neighbor. The actual four-sector
    run normalizes to three shared rays; either the sources are adjacent,
    or the ordinary-middle contradiction applies. See
    `UpperOpenMathN12Recipient.lean`.

The completed `UpperOpenMathDoubleRecipientCurvature.lean` assembles the
parent finite weighted rule and the actual ray identities into the general
all-triple bound

`2 * delta + B15 + J13 >= 2 * U + 3 * E3 + 2 * P21`,

where `delta = n*(n-2)-3*T`, `U` counts unused bounded elementary sides,
`B15` counts `(a,d)=(1,5)` cores, `J13` counts `(1,3)` recipients incident
with two `A0` sources, `E3` counts three-cap cores, and `P21` counts `(2,1)`
cores. It has no component-size bound and requires every core to be triple.
The formal theorem uses integer arithmetic and any injectively indexed
actual triangle certificate. The finite rule is in the parent-owned
`UpperOpenMathDoubleRecipientWeights.lean`; both replay with standard axioms.
The final six-case geometry now proves `J13=0`; the earlier formula is retained
as an independently checked intermediate result. With the improved partial
recipient and N12 charges, the strongest completed actual all-triple endpoint is

`2 * delta + B15 >= 2 * U + 3 * E3 + 3 * P21 + N12`,

where `N12` counts `(a,d)=(1,2)` cores. The actual endpoint is in
`UpperOpenMathN12Curvature.lean`, with the source-chart proof in
`UpperOpenMathN13ActualNoDouble.lean`. These declarations use standard logical
axioms and have no unresolved geometric extraction or source-neighbor premise.
They retain the pairwise-nonparallel and all-triple class restrictions, and do
not solve the unrestricted numerical maximum as a function only of `n`.

For closed core components, `UpperOpenMathClosedN12Curvature.lean` applies the
integer-rounded correction component by component and takes a maximum with
the prior strict/half-gain portfolio. Summing those strongest local lower
costs gives a verified lower bound on `delta-U`. The completed intermediate
`UpperOpenMathClosedDoubleRecipientCurvature.lean` records the same portfolio
construction before elimination of `J13`; all component claims explicitly
require actual shared-core closure and the all-triple class.

Two important limitations were found and retained as exact witnesses:
`adjacent-antipodal-marked-full24.json` allows an `A0` core to touch a marked
full `(2,4,1)` core, and `adjacent-antipodal-full15.json` allows an `A0` core to
touch a full `(1,5,0)` core. Therefore neither exclusion may be broadened to
all full negative-weight neighbors.

The underlying full-fan conclusion that perfect arrangements must be simple
had already been claimed by Clément and Bader. Their auxiliary shared-edge
inequality has explicit counterexamples in this corpus; see
`PERFECT_CORE_ATTRIBUTION.md` and `fp-shared-rule.json`. The statements above
are separately extracted actual geometric resources, rather than an
attribution of that earlier global claim to this session.
