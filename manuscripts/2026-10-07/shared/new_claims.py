"""Scoped principal claims added by the 5--6 October research session.

This inventory distinguishes actual-arrangement endpoints from local interfaces,
native finite certificates, external computation and unformalized analysis.
"""

def extend_claims(add, update, lean, artifact, claims):
    geometric = ("For n>=2 pairwise nonparallel real lines and any finite injective selected "
                 "family of certified triangles, with all inventories extracted from that "
                 "actual arrangement. Counts of unused sides are relative to the selected family. ")
    triple = geometric + "Every core has exactly three supporting lines. "

    def upper(identifier, title, scope, refs, all_triple=True, **extra):
        add(identifier, title, "lean/general", (triple if all_triple else geometric)+scope,
            refs, trust="standard", hypotheses="actual selected certificate; NoParallel; n>=2" +
            ("; all cores triple" if all_triple else ""), **extra)

    update("jext:defect", "lean/general",
        "For each supplied SimpleLowerBound n T with n>=3, actual terminal-ray extraction "
        "proves a simple n+1 witness with the exact deficit-dependent gain g. The proof now "
        "discharges the former boundary and averaging interfaces end to end, uses standard "
        "axioms only, and permits indefinite both-parity iteration. The gain remains input-dependent.",
        lean("OpenMathExtensionFormula", "closed_form_successor")+
        lean("OpenMathEveryOrderExtension", "infinite_quantitative_extension"))
    update("jext:gain", "lean/general",
        "For n>=3 the exact gain is min(floor(n/2),ceil(max(3,max(0,n-delta))/2)), equal "
        "to ceil((n-1)max(3,max(0,n-delta))/(2n)). Actual simple geometry supplies the inputs; "
        "no boundary-count premise is assumed. The finite arithmetic and geometric successor "
        "are both fully checked with standard axioms.",
        lean("OpenMathExtensionFormula", "stepGain_formula", "closed_form_successor"))
    update("jext:odd-near-perfect", "lean/general; inherited special examples",
        "For odd n>=3 every supplied simple witness with delta<=2 admits a successor gaining "
        "floor(n/2). The actual boundary extraction is now complete. The perfect case and "
        "known individual near-perfect examples retain BBL and Blanc attribution; this does "
        "not assert optimal odd seeds at every order.",
        lean("OpenMathBoundarySuccessor", "odd_defect_two_successor")+
        lean("OpenMathOptimalSuccessor", "optimal_odd_to_even", "even_optimality"))
    update("jup:section", "lean/general + scoped ordinary arguments",
        geometric+"All numbered structural endpoints use actual extracted inventories. Simple, "
        "all-triple, parity, degree and component-size hypotheses are retained where stated. "
        "The surviving corrections prevent an unrestricted improved numerical formula. Historical "
        "smoothing classification and remaining equality analysis keep their ordinary-proof tiers.",
        artifact("Kobon/UpperOpenMathGlobalFans.lean")+
        artifact("Kobon/UpperOpenMathMixedCurvatureBound.lean"))
    update("jup:clean", "lean/general",
        "For even n>=4, NoParallel and an injective selected certificate, the actual clean-line "
        "budget n-h<=2U+D1 has a fully extracted charge map and finite fibers. This is distinct "
        "from the newly completed exterior terminal-ray successor, which also has a full actual proof.",
        claims["jup:clean"]["refs"])
    update("jup:budget", "lean/derived",
        "The actual defect identity and clean-line charging yield "
        "2delta>=n+2S-h-3D1-2D2 by algebra. Whole-arrangement fans are now extracted in "
        "the new library and supply the further structural estimates. This row records the "
        "combined budget itself, not an unrestricted numerical upper formula.", claims["jup:budget"]["refs"])
    update("jup:upper", "lean/general",
        "For even n>=4, NoParallel and an injective selected triangle certificate, actual "
        "global fans and boundary budgets prove the retained weighted estimate and the "
        "at-most-two/three-core upper bounds. In particular6T<=n(2n-5)+6 when q<=2 and "
        "6T<=n(2n-5)+12 when q<=3. No abstract fan, boundary or incidence premise remains.",
        lean("UpperOpenMathGlobalFans", "certificate_defect_even")+
        lean("UpperOpenMathBoundaryBudgets", "certificate_two_core_upper", "certificate_three_core_upper"))
    update("jup:weighted", "lean/derived",
        "For even n>=4 actual NoParallel certificates, the completed global fan budget implies "
        "2delta>=n+sum_(r>=3)(2r^2-11r+6)t_r. The underlying extracted theorem is stronger "
        "and retains exceptional-core/shared-core corrections; dropping nonnegative improvements "
        "recovers this old weight. No supplied aggregate geometry remains.",
        lean("UpperOpenMathGlobalFans", "certificate_defect_even"))
    update("jup:two-core", "lean/general",
        "For even n>=4 actual NoParallel certificates with at most two cores, "
        "6T<=n(2n-5)+6, giving the displayed floor upper bound. Core multiplicities are arbitrary. "
        "Actual boundary support, local fans, core paths and parity rounding are discharged in Lean.",
        lean("UpperOpenMathBoundaryBudgets", "certificate_two_core_upper"))
    update("jup:zero-one-core", "lean/derived",
        "For even n>=4 actual NoParallel certificates, q=0 gives delta>=n/2 and q=1 gives "
        "delta>=n/2-1, including a single core of arbitrary multiplicity. Substitute q and "
        "D2=0 into the extracted three-core defect theorem and use integer parity. These are "
        "immediate corollaries; no separately named general one-core wrapper is asserted.",
        lean("UpperOpenMathBoundaryBudgets", "certificate_three_core_defect"))
    update("jup:exceptional", "lean/general",
        "For even n>=4 actual NoParallel injective certificates, "
        "2delta>=n+2S-7I+8q+D2-2e. The exceptional full-fan count e and all local/global "
        "incidences are extracted; the older supplied summed-fan premise has been discharged.",
        lean("UpperOpenMathGlobalFans", "certificate_defect_even"))
    update("jup:sharp-fan", "lean/general + retained local interface",
        "Canonical actual radial fans supply the retained Sectors extremal theorem: "
        "a=2r-3 forces all sectors triangular and d=3, and3a+d<=6r-8+2e. The new actual "
        "summation matches all original triangle occurrences; no whole-arrangement extraction "
        "gap remains for these structural bounds.", claims["jup:sharp-fan"]["refs"]+
        lean("UpperOpenMathGlobalFans", "certificate_weighted_fan_sum"))
    update("jup:high-multiplicity", "lean/general + derived retained comparison",
        "For even n>=4 NoParallel certificates with every core multiplicity at least five, "
        "the actual boundary-sensitive theorem gives a penalized bound stronger than the old "
        "T<=floor(n(n-5/2)/3) comparison. The multiplicity hypothesis is essential; triple and "
        "quadruple weights cannot be treated as nonnegative.",
        lean("UpperOpenMathBoundaryBudgets", "certificate_even_high_five"))
    update("oct:core-budget", "lean/general + retained conditional arithmetic",
        "The formerly conditional aggregate inequality now has an actual counterpart in "
        "GlobalFans. The completed BoundaryBudgets theorem proves6T<=n(2n-5)+12 for even "
        "n>=4 and q<=3. The old arithmetic interfaces remain preserved as implications; actual "
        "geometry now discharges their appropriate stronger endpoint hypotheses.",
        lean("UpperOpenMathGlobalFans", "certificate_defect_even")+
        lean("UpperOpenMathBoundaryBudgets", "certificate_three_core_upper"))
    update("oct:next-proof-plan", "lean/derived with explicit exceptional-triple condition",
        "The earlier next-step graph deductions now follow from completed actual cap-heavy "
        "triple independence and incidence. If every exceptional full fan is triple, then "
        "3e<=D2; substituting into the actual even global budget yields "
        "2delta>=n+2S-7I+8q+e and6delta>=3n+6S-21I+24q+D2. These are immediate "
        "mathematical corollaries, not separately named Lean wrappers. Higher-order extremal "
        "fans are not asserted independent; the condition cannot be dropped.",
        lean("UpperOpenMathCapHeavyTriples", "certificate_cap_heavy_degree_sum")+
        lean("UpperOpenMathGlobalFans", "certificate_defect_even"))
    update("jfam:inherited-families", "external + completed Lean tails",
        "The full q=4*2^s and q=18*2^s odd numerical series retain Forge--Ramirez Alfonsin "
        "and Parpalak--Utkin attribution. Their compatible33/37-line tails now have complete "
        "Lean odd/even family and simple-optimality theorems. The generic actual optimal "
        "odd-to-even theorem supplies the companion from any supplied rounded-optimal simple "
        "odd witness; the whole published series from its smallest seed is not relabeled as "
        "a separately formalized current family theorem.",
        lean("OpenMathConstructionForgeFamily", "odd_family", "even_family")+
        lean("OpenMathConstructionFamily37", "odd_family", "even_family")+
        lean("OpenMathOptimalSuccessor", "optimal_odd_to_even"))

    update("jup:formalization-status", "lean/general + research-frontier",
        geometric+"Canonical radial fans, occurrence matching, component partitions, marked-port "
        "charging and finite geometric escape are now extracted in Lean. The completed structural "
        "bounds retain their class conditions and correction counts. Removing the residual one-cap "
        "correction or proving the proposed global even token trade-off remains open; no new "
        "unrestricted numerical upper formula is claimed.",
        lean("UpperOpenMathMixedCurvatureBound", "certificate_mixed_curvature_component_bound")+
        lean("UpperOpenMathM22Curvature", "certificate_m22_source_free_defect_bound"))
    update("jup:fan", "lean/conditional-interface + actual-extraction",
        "The retained local Sectors inequalities keep their explicit interfaces. The new actual "
        "radial-chart and shared-side matching library supplies their arrangement-level instances "
        "for the structural results below; the former missing global assembly is no longer the "
        "frontier. This does not identify every old proposed aggregate bound with a new theorem.",
        claims["jup:fan"]["refs"]+artifact("Kobon/UpperOpenMathTripleCharts.lean"))
    update("jup:fan-sharp", "lean/conditional-interface + actual-extraction",
        "The local sharper fan inequality d2<=2 implies d1<=2r-4 remains fully checked. Actual "
        "fan extraction and occurrence matching are now completed in the structural library. "
        "This row retains the local theorem's exact interface rather than asserting an unstated "
        "numerical upper bound.", claims["jup:fan-sharp"]["refs"]+
        artifact("Kobon/UpperOpenMathFullTripleChart.lean"))
    update("j:exact49", "lean/general; inherited numerical family",
        "The actual-tangent 49-line uniform seed, simplicity, all 767 listed triangles, axis caps "
        "and 24 visible pairs now feed a complete infinite odd/even geometric family. At "
        "q=48*2^t the counts are 768*4^t-1 and that count plus24*2^t, attaining the classical "
        "simple-model floors. The orbit is a tail of prior BBL constructions, not a new numerical "
        "family. Exact finite native roots remain disclosed in the library audit.",
        lean("BBL49VerifiedFamilies", "seed49_uniform", "seed49_visible_uniform",
             "odd_family", "even_family", "odd_exact", "even_exact"))
    update("oct:forge33", "lean/general; inherited numerical family",
        "The archived compatible 33-line seed is now completed and iterated. For q=32*2^t, "
        "the odd count is (1024*4^t-1)/3 and the even count adds16*2^t; both are optimal in "
        "the simple model. These are the known Forge--Ramirez Alfonsin numerical orbit. The "
        "advance is exact compatible certification and its formal recursion, with finite native "
        "checks explicitly distinguished from standard structural proofs.",
        lean("OpenMathConstructionForgeFamily", "uniform_seed", "uniform_visible_seed",
             "odd_family", "even_family", "odd_optimal_in_simple_arrangements",
             "even_optimal_in_simple_arrangements"))

    add("om:family37", "Completed compatible 37-line known orbit", "lean/general",
        "For every natural t, q=36*2^t gives actual simple witnesses with432*4^t-1 triangles "
        "at q+1 lines and432*4^t-1+18*2^t at q+2. Both meet the simple upper floors. "
        "This is the already known Parpalak--Utkin18-dyadic orbit at its next depth; at38 "
        "its449 simple triangles do not improve the retained450 unrestricted witness.",
        lean("OpenMathConstructionFamily37", "uniform_seed", "odd_family", "even_family",
             "odd_optimal_in_simple_arrangements", "even_optimal_in_simple_arrangements"),
        trust="finite-native-seed + standard recursion")
    add("om:known-orbits", "Completed compatible 33/37/49 numerical orbits", "lean/general; inherited numerical families",
        "For every natural t the compatible33,37,49 seeds give q=32*2^t,36*2^t,48*2^t "
        "with odd counts respectively(1024*4^t-1)/3,432*4^t-1,768*4^t-1, and even "
        "companions adding q/2. All meet the appropriate simple-model upper floors. These "
        "numerical orbits remain attributed to Forge--Ramirez Alfonsin, Parpalak--Utkin/Blanc, "
        "and BBL. Exact compatible seed certification and formal recursive integration are the "
        "current contribution, with native finite roots retained separately from standard upper proofs.",
        lean("OpenMathConstructionForgeFamily", "odd_family", "even_family",
             "odd_optimal_in_simple_arrangements", "even_optimal_in_simple_arrangements")+
        lean("OpenMathConstructionFamily37", "odd_family", "even_family",
             "odd_optimal_in_simple_arrangements", "even_optimal_in_simple_arrangements")+
        lean("BBL49VerifiedFamilies", "odd_family", "even_family", "odd_exact", "even_exact"),
        trust="explicit finite-native seed descendants; standard upper inequalities")
    add("om:family61", "Compatible 61-line seed and preserved 28-pair family", "lean/general",
        "For every natural t, q=60*2^t gives actual simple real-line witnesses of1200*4^t-10 "
        "triangles at q+1 and1200*4^t+30*2^t-12 at q+2. The seed retains1190 triangles, "
        "59 axis caps and28 visible pairs for0<epsilon<=1/100000000 using actual tangent "
        "directions. A positive interval may shrink at each depth. Poola owns the original "
        "61:1190 point count; BBL owns the doubling method. Odd/even existence inherit five/seven "
        "explicit native certificate roots. No absolute numerical-priority assertion is made.",
        lean("OpenMathConstructionFamily61", "uniform_seed", "uniform_visible_seed",
             "odd_family", "even_family", "odd_window", "even_window")+
        artifact("research/openmath-seven-hour-2026-10-05/constructions/construction-proof-provenance.json"),
        trust="five odd / seven even finite native roots + standard recursion")
    add("om:pareto61", "29-pair seed and strongest 60-dyadic even family", "lean/general",
        "The compatible seed still has1190 triangles and59 axis caps, now with29 visible pairs. "
        "For every natural t, V_t=30*2^t-1 and the even family is "
        "1200*4^t+30*2^t-11 at60*2^t+2 lines, exactly one above the preserved28-pair family "
        "at every depth. The odd count remains1200*4^t-10. The simple upper gaps are9/10. "
        "The new even witness at62 is1219, below the retained1220 baseline. Seven explicit "
        "native finite roots support the seed; recursive geometry is standard.",
        lean("OpenMathConstructionParetoFamily61", "uniform_visible_seed", "visible_formula",
             "odd_family", "even_family", "even_polynomial", "improves_prior_even_family",
             "even_window"), trust="seven finite native roots + standard recursion")
    add("om:construction-envelope", "Pointwise retained all-natural-order construction portfolio", "lean/general",
        "The executable maximum retains RecursiveEnvelope.bound and the33,37,49,61 odd/even "
        "candidates over0<=t<=n. For every natural n it gives an actual LowerBound, never below "
        "the previous envelope or baseline. The61 gains over G are20*2^t-11 odd and "
        "10*2^t-11 even for t>=1. Comparisons with G and the old28-pair family are exact; "
        "they do not imply strict improvement over every prior portfolio candidate or literature bound.",
        lean("OpenMathConstructionEnvelope", "bound", "all_n", "previous_le", "baseline_le",
             "retains_old_even_family_plus_one", "odd_baseline_gain", "even_baseline_gain"),
        trust="explicit finite-native seed descendants + standard maximum argument")
    update("j:new-envelope", "lean/general",
        "The October7 construction portfolio is a LowerBound at every natural order, retains "
        "the previous RecursiveEnvelope pointwise, and adds the33/37/49/61 candidates over0<=t<=n. "
        "The former ten-dyadic strict-tail comparison remains proved and retained. New61 gains "
        "are stated against G or the preserved28-pair family; no blanket strict comparison with "
        "all preceding candidates or all literature is inferred.",
        claims["j:new-envelope"]["refs"]+
        lean("OpenMathConstructionEnvelope", "all_n", "previous_le", "bound"))
    add("om:boundary-budget", "Actual terminal-resource identities", "lean/general",
        "For simple NoParallel real arrangements and an injective selected triangle family, "
        "n>=3: A+2B=2n, A<=2U, delta=U, and B>=n-delta, where terminal incidences are "
        "extracted from sorted actual crossing vertices. Every simple arrangement also has B>=3. "
        "No exterior-visibility or convex-hull oracle is a premise.",
        lean("OpenMathSimpleBoundary", "terminal_partition", "certificate_single_terminal_budget",
             "certificate_double_terminal_budget", "certificate_boundary_defect")+
        artifact("Kobon/OpenMathBoundaryMinimum.lean"), trust="standard")
    add("om:successor", "Indefinite simple successor with deficit-dependent gain", "lean/general",
        "For every supplied SimpleLowerBound n T with n>=3, set signed delta=n(n-2)-3T "
        "and b=max(3,max(0,n-delta)). There is a simple real straight-line witness at n+1 "
        "with at least T+g triangles, where g=min(floor(n/2),ceil(b/2)). The same g equals "
        "ceil((n-1)b/(2n)); natural subtractions in the implementation truncate at zero. "
        "Actual terminal rays, critical roots and integer averaging discharge all visibility premises.",
        lean("OpenMathExtensionFormula", "stepGain_formula", "closed_form_successor")+
        lean("OpenMathEveryOrderExtension", "successor"), trust="standard")
    add("om:successor-iteration", "Both-parity indefinite quantitative iteration", "lean/general",
        "Starting from any supplied simple n>=3 seed, the count recurrence T_(k+1)=T_k+g(n+k,T_k) "
        "gives actual SimpleLowerBound witnesses at every later order. For n>=4 each step gains "
        "at least two and hence T_k>=T+2k. This does not prove a half-order gain for arbitrary "
        "seeds; its numerical envelope may be weaker than the established quadratic baseline.",
        lean("OpenMathEveryOrderExtension", "stepGain_at_least_two", "infinite_linear_extension",
             "iteratedCount", "infinite_quantitative_extension"), trust="standard")
    add("om:perfect-successor", "Near-perfect odd successor and simple optimality", "lean/general",
        "For odd n=2m+1>=3, a supplied simple witness with delta<=2 has a successor gaining m. "
        "A supplied witness attaining the odd simple upper floor therefore has a successor "
        "attaining the even simple floor. The existence of such an optimal input is a premise; "
        "optimal odd seeds are not asserted at every order. BBL's older perfect exterior step "
        "and Blanc's individual near-perfect examples remain credited.",
        lean("OpenMathBoundarySuccessor", "odd_defect_two_successor")+
        lean("OpenMathOptimalSuccessor", "optimal_odd_to_even", "even_optimality"), trust="standard")

    upper("om:ray-resources", "Exact actual ray and defect resources",
        "The actual resource identities are D1+2D2+C+Rc=2I and "
        "2delta=2 sum_core r(r-3)+2U+C+Rc-D1. C counts bounded nonshared core endpoints "
        "and Rc actual unbounded core rays; arbitrary core multiplicities are allowed.",
        lean("UpperOpenMathRayResources", "certificate_ray_resource_identity", "certificate_defect_ray_identity"), False)
    upper("om:component-hull", "Actual component hull deficit penalty",
        "With b_h the sum of supporting hull-point counts of the actual shared-core components, "
        "2delta>=2U+2 sum_(r>=3)r(r-4)t_r+3q+3b_h. Each supported core consumes actual "
        "nonshared/ray resources. For all core multiplicities at least R>=4 this gives "
        "6T+(2R(R-4)+3)q+3b_h+2U<=2n(n-2). No convex-hull oracle is assumed.",
        lean("UpperOpenMathComponentHullDeficit", "certificate_component_hull_deficit"), False)
    upper("om:triple-cap", "Actual triple-cap transfer budget",
        "D1+2E3+P21<=2q and delta>=U+q-D2+2E3+P21. Marked shared rays transfer actual "
        "source capacity to poor targets; no cap-count hypothesis is assumed.",
        lean("UpperOpenMathTripleCapBudget", "certificate_triple_cap_budget", "certificate_triple_cap_defect"))
    upper("om:cap-heavy", "Actual cap-heavy triple independence and incidence",
        "Cap-heavy triple sources cannot be adjacent across an actual shared-core side. Their "
        "core-degree sum consumes distinct actual core-to-core edges. Other core multiplicities "
        "are unrestricted. Full extremal triples contribute three incidences; the statement "
        "does not assert independence of higher-multiplicity extremal fans.",
        lean("UpperOpenMathCapHeavyTriples", "certificate_cap_heavy_not_adjacent",
             "certificate_cap_heavy_degree_sum"), False)
    upper("om:mixed-cap", "Mixed multiplicity weighted cap budget",
        "With Q=sum_(r>=4)(r(r-4)+1) and P the poor-triple core-degree sum, "
        "3D1+3q+3Q+2P<=3S and3delta>=3(U+q-D2+Q)+2P. Higher extremal fans need "
        "not be independent; their multiplicity surplus supplies the charge.",
        lean("UpperOpenMathMixedCapBudget", "certificate_mixed_weighted_budget",
             "certificate_mixed_weighted_defect", "certificate_mixed_core_defect"), False)
    upper("om:mixed-curvature", "Degree-free mixed component curvature",
        "For arbitrary multiplicities, degrees and component sizes, "
        "delta+Aall+sum_s ceil(B_s/2)>=U+c+h, with h=sum_(r>=4)r(r-4). "
        "Aall counts all full(2,4) triple cores and B_s full(1,5) triples. The doubled companion "
        "is2delta+2Aall+B>=2U+c+2h. Every component includes its isolated core vertices. "
        "Corrections are retained; they cannot be discarded for a universal numerical upper bound.",
        lean("UpperOpenMathMixedCurvatureBound", "certificate_mixed_curvature_component_bound",
             "certificate_mixed_doubled_component_bound"), False)
    upper("om:paid-curvature", "Degree-free marked all-triple component curvature",
        "delta+A0+sum_s ceil(B_s/2)>=U+c, where A0 counts only unmarked full(2,4) triples. "
        "The actual marked-port payment and finite escape proof exclude the zero paid case. "
        "No degree, independence or component-size hypothesis is imposed.",
        lean("UpperOpenMathPaidCurvatureBound", "certificate_component_half_penalty_bound",
             "certificate_half_exception_bound"))
    upper("om:half-curvature", "Retained half-coefficient and gain portfolio",
        "2delta+A0+B>=2U; a stronger gain version has "
        "4delta+2A0+2B>=4U+6E3+5P21. The component maximum retains strict paid curvature "
        "and the rounded gain score before summing; Lean proves its dominance over the older hybrid. "
        "These intermediate formulas are retained even where the later N12 theorem is stronger.",
        lean("UpperOpenMathHalfCurvature", "certificate_half_defect_bound")+
        lean("UpperOpenMathHalfCurvatureGain", "certificate_half_gain_defect_bound")+
        lean("UpperOpenMathClosedHalfCurvature", "certificate_hybrid_component_defect",
             "certificate_hybrid_gain_component_defect", "hybrid_gain_dominates"))
    upper("om:n13-global", "Source-free all-triple defect gain",
        "An actual(1,3) recipient has at most one antipodal full source neighbor, eliminating "
        "J13. A(2,1) recipient has none. Hence2delta+B>=2U+3(E3+P21), with no component "
        "size or degree restriction. The corresponding source-free component score is also proved.",
        lean("UpperOpenMathN13ActualNoDouble", "certificate_n13_no_two_anti_neighbors")+
        lean("UpperOpenMathPartialRecipients", "certificate_partial_anti_degree_zero")+
        lean("UpperOpenMathN13Curvature", "certificate_source_free_defect_bound",
             "certificate_source_free_hybrid_component_defect"))
    upper("om:n12-global", "N12 all-triple positive gain",
        "An actual(1,2) recipient has at most one antipodal source neighbor. "
        "Therefore2delta+B>=2U+3(E3+P21)+N12, with no degree or component-size restriction. "
        "This is an actual arrangement endpoint, not a supplied radial-interface implication.",
        lean("UpperOpenMathN12Recipient", "certificate_n12_anti_degree_le_one")+
        lean("UpperOpenMathN12Curvature", "certificate_n12_source_free_defect_bound"))
    upper("om:n12-components", "Strongest completed all-triple component portfolio",
        "delta>=U+sum_s max(1-A_s-ceil(B_s/2), "
        "ceil((3E_s+3P_s+N12_s-B_s)/2)). All counts are taken within each actual connected "
        "component before rounding or taking the maximum. Lean proves dominance over the preceding "
        "source-free portfolio. This component theorem contains no M22 term.",
        lean("UpperOpenMathClosedN12Curvature", "certificate_closed_n12_source_free_gain",
             "certificate_n12_source_free_hybrid_component_defect", "source_free_n12_dominates"))
    upper("om:m22-global", "Strongest completed global marked-balanced gain",
        "With M22 counting marked(2,2) cores, the proved global endpoint is "
        "2delta+B>=2U+3(E3+P21)+N12+M22. The local actual incident-edge competition "
        "m+degreeFrom(A0,p)<=d makes the marked balanced gap positive. M22 is currently "
        "retained globally; no componentwise M22 portfolio is asserted.",
        lean("UpperOpenMathLocalPortBudget", "certificate_marked_plus_anti_degree_le")+
        lean("UpperOpenMathM22Curvature", "certificate_m22_source_free_defect_bound"))
    upper("om:profile-positive", "Explicit positive-profile sufficient condition",
        "If every component satisfies B_s+1<=3E_s+3P_s+N12_s, then delta>=U+c. "
        "The condition is an explicit hypothesis about actual extracted profiles, not a theorem "
        "that every component has it. Arbitrarily large components and degrees are permitted.",
        lean("UpperOpenMathPositiveProfileComponents", "certificate_positive_profile_component_defect"))
    upper("om:mixed-degree3", "Mixed degree-at-most-three strict curvature",
        "If every shared-core degree is at most3, delta>=U+c+h. Arbitrary multiplicities, "
        "component sizes, branching and cycles are allowed; actual equality geometry supplies "
        "one positive unit per component.",
        lean("UpperOpenMathMixedDegreeThree", "certificate_mixed_degree_three_component_bound"), False)
    upper("om:mixed-degree4", "Mixed degree-at-most-four strict curvature",
        "If every shared-core degree is at most4, delta+Aall>=U+c+h. The full(2,4) "
        "triple correction remains; components can have arbitrary order and multiplicities.",
        lean("UpperOpenMathMixedDegreeFour", "certificate_mixed_degree_four_component_bound"), False)
    upper("om:five-components", "Five-core component strict bounds",
        "If every actual shared-core component has at most5 vertices, delta>=U+c+h for "
        "arbitrary multiplicities, and delta>=U+c in the all-triple subclass. The total number "
        "of cores and components is unrestricted. Perfect-implies-simple in this sufficient "
        "scope formalizes a conclusion already stated by Clement--Bader, with no first-discovery claim.",
        lean("UpperOpenMathMixedFiveCoreComponents", "certificate_mixed_five_component_bound",
             "certificate_mixed_five_component_perfect_simple")+
        lean("UpperOpenMathFiveCoreComponents", "certificate_five_core_component_bound"), False)
    upper("om:forest", "Actual shared-core forest bounds",
        "If the actual shared-core graph is acyclic, D2+c=q. With arbitrary degrees and "
        "multiplicities delta>=U+c+Q and3delta>=3(U+c+Q)+2P; in the all-triple class "
        "delta>=U+c+2E3+P21. This includes branching trees of arbitrary size.",
        lean("UpperOpenMathForestBudget", "certificate_forest_edge_component_count",
             "certificate_triple_forest_bound", "certificate_mixed_forest_bound",
             "certificate_mixed_forest_weighted_bound"), False)
    upper("om:graph-classes", "Retained actual degree, order and forest portfolio",
        "The proved class corollaries retain delta>=U+c+h at shared-core degree<=3 or "
        "component order<=5; at degree<=4 they retain the Aall correction. Forests instead "
        "retain the mixed weighted cap bound and the stronger all-triple positive cap terms. "
        "Each restriction is stated separately; no class condition is silently dropped.",
        lean("UpperOpenMathMixedDegreeThree", "certificate_mixed_degree_three_component_bound")+
        lean("UpperOpenMathMixedDegreeFour", "certificate_mixed_degree_four_component_bound")+
        lean("UpperOpenMathMixedFiveCoreComponents", "certificate_mixed_five_component_bound")+
        lean("UpperOpenMathForestBudget", "certificate_mixed_forest_weighted_bound",
             "certificate_triple_forest_bound"), False)
    upper("om:antipodal-intersection", "Two antipodal sources share at most two neighbors",
        "Two distinct antipodal full triple sources have at most two common actual core neighbors. "
        "Only the source cores must be triple; neighbors may have arbitrary multiplicity. "
        "Strict cevian crossing and elementary-segment blocking supply the geometry.",
        lean("UpperOpenMathAntipodalThreeNeighbors", "certificate_common_neighbor_card_le_two"), False)
    upper("om:seven-components", "At-most-one-source and seven-core component portfolios",
        "A component with at most7 core vertices has at most one antipodal source. "
        "The proved score ceil((3E_s+2P_s-B_s)/2) applies under that source condition, "
        "and the adaptive theorem retains the preceding score otherwise. The B correction "
        "cannot be omitted to claim delta>=U+c for all seven-core components.",
        lean("UpperOpenMathSingleSourceComponents", "certificate_seven_core_single_source",
             "certificate_adaptive_component_defect", "certificate_seven_component_defect"))
    upper("om:n13-support", "Actual affine-maximum exclusion for N13 recipients",
        "A(1,3) core with an antipodal source neighbor cannot maximize an affine functional "
        "injective on an actual finite closed core set containing it. This completed boundary "
        "lemma does not exclude an N13 neighbor of a maximum balanced core or prove every "
        "component strictly positive without corrections.",
        lean("UpperOpenMathN13ActualSupportExtreme", "certificate_n13_positive_anti_degree_not_max"))
    upper("om:even-line-budget", "Safe actual all-line parity budget",
        "For even n>=4, n<=2U+2D1+C. A shared core-ordinary side may pay as both a "
        "transverse charge and a base; dropping the second D1 is false. The stronger token "
        "trade-off and C>=2D1 remain research hypotheses rather than inputs to current theorems.",
        lean("UpperOpenMathOrdinaryGlobalCharge", "certificate_all_line_parity_budget"))

    add("om:translation-germs", "Exact simultaneous triangle classification under line translation", "lean/general",
        "For any finite pairwise nonparallel actual real arrangement, translating one line "
        "makes the determinant-side evaluations affine in epsilon. A common positive threshold "
        "classifies every supporting triple exactly by its constant and linear coefficients. "
        "This is a general real-parameter proof with standard axioms only.",
        lean("OpenMathTranslationGerms", "eval_translate_affine", "side_translate_affine",
             "simultaneous_triangle_stability"), trust="standard")
    add("om:translation-identity", "Global exact birth/loss count and retention criterion", "lean/general",
        "For sufficiently small positive epsilon, T(epsilon)+lost=T(0)+born, with complete "
        "global germ birth/loss sets. The untouched-corner/stationary-zero conditions imply "
        "no loss and, with an appropriate tiny triangle, a one-triangle gain. These retention "
        "conditions are explicit; a half-plane count is not substituted for the loss set.",
        lean("OpenMathTranslationCounting", "translated_birth_loss_identity")+
        lean("OpenMathTranslationRetention", "no_loss_count", "classical_gain_one"), trust="standard")
    add("om:isolated-birth", "Exact isolated concurrent-triple birth", "lean/general",
        "Under NoParallel and an explicitly unique concurrent supporting triple, moving its "
        "incident line in the specified sign direction produces exactly one germ birth. "
        "The resulting identity retains the exact global loss count; it asserts no universal "
        "bound of two on losses.",
        lean("OpenMathTripleBirth", "tiny_triangle_germ")+
        lean("OpenMathIsolatedTripleResolution", "unique_birth_card", "isolated_resolution_identity"), trust="standard")
    add("om:four-line", "Exact four-line counterexample to the specified half-plane yield formula", "lean/general",
        "For y=0,y=x,y=-x,2x+y=2, the sole triple point is isolated and all other vertices "
        "ordinary. Both old triangle interiors have x-y>0. Replacing y=x by y=x+epsilon "
        "for every0<epsilon<1 leaves exactly two triangles although the stated moved-side "
        "half-plane count is zero and Liu v1 Theorem1.1 predicts three. This refutes only "
        "that formula within its stated scope, not unrelated claims in the preprint.",
        lean("OpenMathFourLineResolution", "old_unique_triple", "old_interiors_positive",
             "negative_count_zero", "moved_count", "halfplane_yield_fails")+
        artifact("research/openmath-seven-hour-2026-10-05/corpus/DESINGULARIZATION_AUDIT.md"), trust="standard")
    add("om:six-line", "Exact six-line translation and reverse wall crossing", "lean/general",
        "For the explicit six-line arrangement and every0<epsilon<1/100, the old count is6, "
        "upward resolution gives7 and downward resolution4. The latter loses three alternating "
        "old triangles and creates one; its reverse gains two. The entire open intervals, "
        "NoParallel and old isolated triple are kernel proved with standard axioms.",
        lean("OpenMathSixLineResolution", "old_count", "up_count", "down_count",
             "reversal_gain_two", "downward_breaks_three", "old_unique_triple"), trust="standard")
    add("om:analytic-checkers", "Standard analytic boxes and sound finite-check infrastructure", "lean/general",
        "Actual tan(k*pi/60), k=1..29 and tan(k*pi/36), k=1..17 are enclosed by explicit "
        "rational bounds using standard analytic lemmas and kernel arithmetic. Memoized Boolean "
        "and sparse integer box checks are proved extensionally equal/sound for the original "
        "geometric predicates. Executed finite seed equalities retain their separate native trust.",
        lean("BBLTangent60Bounds", "tan_1_bounds", "tan_29_bounds")+
        lean("BBLTangent36Bounds", "tan_1_bounds", "tan_17_bounds")+
        lean("OpenMathConstructionBooleanMemo", "simple_sound", "triangles_sound", "visibles_sound")+
        lean("OpenMathIntegerSparseBoxes", "support_card_le_three", "simpleSparse_sound"), trust="standard")
    add("om:cell41-dual", "Exact prescribed 41-line sign-cell dual obstruction", "computation",
        "An exact small-epsilon positive-dependence certificate excludes only the exported "
        "normalized41-line sign cell. The concrete coefficients and checks are external "
        "exact arithmetic; the general StrictLinearCertificate lemma does not turn this "
        "specific41-line artifact into a Lean theorem. No all41-arrangement impossibility is claimed.",
        artifact("research/openmath-seven-hour-2026-10-05/constructions/parametric-farkas-cell41.json"))
    add("om:equality-analysis", "Remaining zero-component saturation analysis", "manuscript/research-plan",
        "The equality decomposition and saturated poor-profile reduction are mathematical "
        "analysis recorded after the N12 and local-port proofs. The R22-to-N13 and R22-to-R04 "
        "boundary coupling cases remain unproved. N13's own affine-maximum exclusion does not "
        "exclude it as a neighbor of an R22 maximum. No new Lean equality theorem or unconditional "
        "positive component correction is inferred.",
        artifact("research/openmath-seven-hour-2026-10-05/constructions/remaining-zero-component-analysis.md"))
    add("om:searches", "Source-pinned bounded construction and curvature experiments", "computation + external-input",
        "The retained cap-cone, fixed-axis nesting, corridor insertion, deletion, projective-chart, "
        "LP and mutation screens specify their inputs and search limits. Their failures do not "
        "prove general infeasibility or nonstretchability. Exact counterexamples refute selected "
        "shared-side/token/independence shortcuts; abstract finite charging equality graphs are "
        "not thereby geometrically realizable. Primary contestant sources and individual input "
        "credits are preserved rather than adopting the judging archive as a theorem oracle.",
        artifact("research/openmath-seven-hour-2026-10-05/corpus/TECHNIQUES_AND_OBSTRUCTIONS.md")+
        artifact("research/openmath-seven-hour-2026-10-05/corpus/source-inventory.json")+
        artifact("research/openmath-seven-hour-2026-10-05/seed_search/STRUCTURAL_PROBES.md"))

    for identifier in ("jext:defect", "jext:gain", "jext:odd-near-perfect", "jup:section",
        "jup:clean", "jup:budget", "jup:upper", "jup:weighted", "jup:two-core",
        "jup:zero-one-core", "jup:exceptional", "jup:sharp-fan", "jup:high-multiplicity",
        "jup:formalization-status", "jup:fan", "jup:fan-sharp", "oct:core-budget", "oct:next-proof-plan"):
        claims[identifier]["trust"] = "standard"
