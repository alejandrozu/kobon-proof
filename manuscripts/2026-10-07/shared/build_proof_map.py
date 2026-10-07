"""Build the October claim/source map, retaining every September claim identity.

Run from any working directory with standard Python. All mathematical and
experimental references are verified against immutable Git blobs. This is a
provenance/statement-scope audit, not a substitute for the recorded Lean build.
"""
from __future__ import annotations

import copy
import hashlib
import io
import json
import re
import subprocess
from pathlib import Path
from new_claims import extend_claims

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PIN = "f44f23ee062a255f5cad7d39188fd55c0feb83a8"
# Verification records can be committed after the frozen mathematical sources.
VERIFICATION_PIN = "af74635d8b25b32703088460bc41854bb18e1a05"
URL = "https://github.com/alejandrozu/kobon-proof/blob/" + PIN + "/"
SOURCE = ROOT / "paper/journal/proof_map.json"


def read(path):
    return (ROOT / path).read_text(encoding="utf-8-sig")


def declaration_line(path, declaration):
    """Locate a declaration's source line, allowing nested namespace spelling."""
    pieces = declaration.split(".")
    patterns = [re.compile(r"(?:^|\s)(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+"
                           + re.escape(".".join(pieces[k:])) + r"(?=\s|[:({\[]|$)")
                for k in range(len(pieces))]
    candidates = [(i, line) for i, line in enumerate(read(path).splitlines(), 1)
                  if any(pattern.search(line) for pattern in patterns)
                  and not line.lstrip().startswith(("--", "/-", "*"))]
    if len(candidates) != 1:
        raise ValueError(f"Expected unique declaration {declaration} in {path}: {candidates}")
    return candidates[0][0]


def reference(path, declaration="", line=1):
    if declaration:
        line = declaration_line(path, declaration)
    blob = (ROOT / path).read_bytes()
    commit = VERIFICATION_PIN if path.startswith("verification/") or path.endswith("RELEASE_VERIFICATION.json") else PIN
    return dict(path=path, declaration=declaration, line=line, commit=commit,
                source_sha256=hashlib.sha256(blob).hexdigest(),
                url=f"https://github.com/alejandrozu/kobon-proof/blob/{commit}/{path}#L{line}")


def lean(module, *names):
    return [reference(f"Kobon/{module}.lean", f"Kobon.{module}.{name}") for name in names]


def artifact(path):
    return [reference(path)]


def pinned_blobs(paths, commit=PIN):
    process = subprocess.run(["git", "cat-file", "--batch"], cwd=ROOT,
        input="".join(f"{commit}:{path}\n" for path in paths).encode("utf-8"),
        capture_output=True, check=True)
    stream = io.BytesIO(process.stdout)
    answer = {}
    for path in paths:
        header = stream.readline().decode("utf-8").split()
        if len(header) != 3 or header[1] != "blob":
            raise ValueError(f"Invalid pinned blob header {path}: {header}")
        answer[path] = stream.read(int(header[2]))
        assert stream.read(1) == b"\n"
    return answer


def generate():
    previous = json.loads(SOURCE.read_text(encoding="utf-8"))
    data = copy.deepcopy(previous)
    data.update(date="2026-10-07", math_commit=PIN, verification_commit=VERIFICATION_PIN,
                scope="Updated claim-to-source and coverage audit for both October manuscripts. "
                "Preserves all 89 historical and all 160 October 3 claim identities, and all 138 finite coordinate identities. "
                "Completed Lean, conditional Lean, ordinary arguments, external exact computations "
                "and unfinished drafts are distinguished; manuscript editing adds no Lean theorem.")
    data["latest_confirmed_proof_ci"] = dict(commit="2d69a71e32d3eaa59399b0e5bc61720ec3b00ac8", run=37056093885,
        conclusion="success", url="https://github.com/alejandrozu/kobon-proof/actions/runs/37056093885")
    summary = json.loads(read("verification/lean-summary.json"))
    audit = summary["whole_project_axiom_audit"]
    data["proof_verification"] = dict(complete=summary["complete"], mode=summary["mode"],
        checked_at_utc=summary["checked_at_utc"], baseline=summary["baseline"],
        verification_modes=summary["verification_modes"],
        clean_ci_rebuild=summary.get("clean_ci_rebuild"),
        limitation="Unchanged source/import closures reuse a verified baseline; current local verification is not a clean rebuild of every module. CI status is recorded separately.")
    data["release_counts"] = dict(active_lean_sources=len(summary["source_sha256"]),
        build_targets=len(summary["results"]), audited_theorems=audit["theorems"],
        standard_axioms_only=audit["standard_axioms_only"],
        native_descendants=audit["native_evaluation_dependent"],
        finite_coordinate_identities=138, simple_coordinate_identities=104)
    claims = {claim["id"]: claim for claim in data["claims"]}
    for claim in data["claims"]:
        claim["previous_status"] = claim["status"]
        claim["refs"] = [reference(ref["path"], ref["declaration"], ref["line"])
                         for ref in claim["refs"]]
    for row in data["finite_catalog"]:
        row["refs"] = [reference(ref["path"], ref["declaration"], ref["line"])
                       for ref in row["refs"]]

    def update(identifier, status, scope, refs=None, title=None):
        claim = claims[identifier]
        claim.update(status=status, scope=scope)
        if refs is not None:
            claim["refs"] = refs
        if title:
            claim["title"] = title

    def add(identifier, title, status, scope, refs, **extra):
        if identifier in claims:
            raise ValueError(identifier)
        claim = dict(id=identifier, title=title, status=status, scope=scope, refs=refs, **extra)
        data["claims"].append(claim)
        claims[identifier] = claim

    update("j:cell", "partial", "Under global NoParallel, Lean proves nonempty triangle interiors, "
        "equality with the strict sign cell, and pairwise disjointness. The manuscript's ordinary "
        "convexity and connected-component argument supplies the topological interpretation. "
        "The October wording uses the global nonparallel hypothesis rather than enlarging the Lean theorem.")
    update("j:44equality", "lean/derived", "The retained finite SimpleLowerBound 44 608 certificate "
        "and the now-formalized simple even upper theorem imply exact simple optimality by substitution "
        "44*(2*44-5)/6=608. This is an immediate mathematical corollary of the linked Lean theorems; "
        "there is no separately named 44-line optimality wrapper. It makes no nonsimple optimality "
        "or first numerical priority claim.", claims["j:44equality"]["refs"] +
        lean("UpperEvenSimpleOptimality", "simple_lower_bound_even_floor"))
    family_refs = lean("BBLVerifiedFamilies", "eleven_odd_family", "eleven_even_family")
    family_scope = ("For every natural t, q=10*2^t gives actual simple real-line witnesses "
        "of (q^2-4)/3 triangles at q+1 lines and (q^2-4)/3+q/2 at q+2 lines. "
        "All geometric seed and visibility hypotheses are discharged. At each finite depth the "
        "proof may choose a smaller positive epsilon interval; it asserts neither one fixed epsilon "
        "for all depths nor a successor rule for an arbitrary input arrangement. Concrete odd/even "
        "families inherit four/six existing native checks, respectively. BBL doubling is inherited; "
        "the completed recursive formalization is not a new numerical-record claim.")
    update("jfam:families", "lean/general", family_scope, family_refs,
           "Completed odd and stronger even q=10*2^t geometric families")
    update("jfam:strong-even", "lean/general", family_scope,
           lean("BBLVerifiedFamilies", "eleven_even_family"))
    update("jfam:recursive-components", "lean/general", "The recursive seed record now closes "
        "under actual geometric doubling, including the grid, saturation, positive apex, simplicity, "
        "triangle-list transport and exterior visibility. The generic theorems retain an explicit "
        "uniform seed premise; the concrete 21-line seed discharges it.",
        lean("BBLRecursiveSeed", "seed_step") + lean("BBLEvenRecursive", "visible_seed_step") +
        lean("BBLInfinite", "uniform_iterate") + lean("BBLEvenInfinite", "uniform_iterate"))
    update("jfam:large-completed", "lean/general + computation", "The numerical lower bounds "
        "321:34132, 322:34292 and 641:136532 are now consequences of the complete infinite Lean "
        "families. The previously saved coordinate files independently passed two external exact "
        "counters, but are not thereby retroactively included in the finite Lean certificate catalog.",
        family_refs + claims["jfam:large-completed"]["refs"])
    update("jfam:large-incomplete", "lean/general + pending-coordinate-check", "The existence of "
        "a simple 642-line arrangement with 136852 triangles is now proved by the infinite even "
        "family. The earlier saved 642-line coordinate file's unfinished second counter remains "
        "unfinished; the existence theorem does not certify that particular file.",
        lean("BBLVerifiedFamilies", "eleven_even_family") + claims["jfam:large-incomplete"]["refs"],
        "642:136852 existence proved; old individual coordinate verification remains separate")
    update("jup:identity", "lean/general", "For n>=2 pairwise nonparallel actual real lines and "
        "any finite injective certified triangle family, Lean extracts the actual vertices, bounded "
        "elementary segments, shared endpoints and multiplicities, and proves E=n(n-2)-S, "
        "3T=E-U+D1+D2 and delta=S+U-D1-D2. Unused/shared are relative to the selected family, "
        "which need not enumerate all triangular cells. No global incidence identity is assumed.",
        lean("UpperEdgeInventory", "edge_cardinality", "certificate_defect_identity") +
        lean("UpperTriangleIncidence", "certificate_incidence") +
        lean("UpperSharedEdge", "Pair.not_both_endpoints_ordinary"))
    update("jup:clean", "lean/general", "For even n>=4 pairwise nonparallel real lines and any "
        "finite injective certified triangle family, n-h<=2U+D1 is extracted from actual clean-line "
        "crossings and bounded-edge pairing. The charge map and its finite fibers are proved, "
        "without a charging hypothesis. This upper-bound charging is distinct from the still "
        "partly formalized exterior-boundary gain argument.",
        lean("UpperCleanCharging", "certificate_clean_line_budget") +
        lean("UpperCleanCover", "certificate_clean_line_charge"))
    update("jup:budget", "lean/derived", "The earlier combined defect budget follows by algebra "
        "from the actual extracted defect identity and clean-line charging. The linked arithmetic "
        "lemma can now receive these geometric inputs; it is not an unrestricted improved numerical "
        "upper bound without the remaining fan estimate.",
        claims["jup:budget"]["refs"] + lean("UpperEdgeInventory", "certificate_defect_identity") +
        lean("UpperCleanCharging", "certificate_clean_line_budget"))
    update("jup:fan-sharp", "lean/conditional-interface", "The stronger local statement "
        "d2<=2 implies d1<=2r-4 is now proved for an explicit actual cyclic Sectors interface. "
        "This includes the earlier d2<=1 case. Whole-arrangement construction and incidence "
        "matching of every fan remain separate obligations.",
        lean("UpperFan", "Sectors.ordinary_shared_card_le_of_core_le_two"),
        "Sharper actual local fan theorem for at most two core-ended shared rays")
    update("jup:fan", "lean/conditional-interface", "The local real-geometry cyclic-fan "
        "interfaces prove d1<=2r-3 and3d1+d2<=6r-6. The new equality analysis proves "
        "that d1=2r-3 forces every sector triangular and exactly d2=3, so d2<=2 implies "
        "d1<=2r-4. Whole-arrangement extraction and matching of these interfaces remains "
        "unfinished, independently of the completed incidence and charging theorems.",
        lean("UpperFan", "Sectors.ordinary_shared_card_le",
            "Sectors.core_shared_card_eq_three_of_extremal",
            "Sectors.ordinary_shared_card_le_of_core_le_two", "Sectors.weighted_local_bound"))
    update("jup:formalization-status", "partial", "Completed: elementary-side extraction, side "
        "capacity, multiplicity and defect identities, core incidences, actual clean-line charging, "
        "both classical simple upper bounds, actual local fan rigidity and sharper local counts. "
        "Remaining: canonical whole-arrangement cyclic-fan extraction, matching across shared "
        "edges and global summation for the proposed general nonsimple bounds. Conditional "
        "aggregate arithmetic is not an unconditional new upper theorem.",
        lean("UpperEdgeInventory", "certificate_defect_identity") +
        lean("UpperCleanCharging", "certificate_clean_line_budget") +
        lean("UpperEvenSimpleOptimality", "simple_lower_bound_even_floor") +
        lean("UpperCoreBoundary", "CoreFamily.sum_ordinary_bound"))
    update("j:blanc", "lean/general; inherited theorem", "The classical simple even bound "
        "T<=floor(n(2n-5)/6) is now proved from actual geometry for every SimpleLowerBound witness "
        "of even n>=4. Blanc's prior mathematical result remains attributed; this release adds "
        "its complete formalization. The simplicity hypothesis is essential.",
        lean("UpperEvenSimpleOptimality", "simple_lower_bound_even_upper", "simple_lower_bound_even_floor"))

    add("jfam:recursive", "Closed geometric recursive seed and visibility invariants", "lean/general",
        family_scope, lean("BBLRecursiveSeed", "seed_step") +
        lean("BBLEvenRecursive", "visible_seed_step") +
        lean("BBLInfinite", "uniform_iterate", "infinite_family", "triangleCount_identity") + family_refs)
    add("jfam:windows", "Actual one-triangle optimality windows for simple arrangements", "lean/general",
        "For each q=10*2^t both family counts are attainable in simple arrangements, and every "
        "SimpleLowerBound witness at the same order has at most the constructed count plus one. "
        "Upper halves use only standard axioms; existence inherits the recorded native checks. "
        "The window is specific to simple arrangements and need not mean that exact optimum is "
        "unknown at every small order.", lean("BBLFamilyOptimality", "odd_window", "even_window"))
    add("j:new-envelope", "All-natural-order envelope retaining the completed recursive families", "lean/general",
        "H(n)=max(B(n),L(n)) is a LowerBound for every natural n, where B is the former "
        "finite-enhanced envelope and L selects the two recursive family counts. A finite "
        "maximum over t<n+1 implements the definition. H>=B everywhere and strictly exceeds "
        "B on both dyadic tails from orders321 and322. These are gains over the previous "
        "verified repository envelope, not claims of improving all published constructions.",
        lean("RecursiveEnvelope", "all_n", "previous_le", "strict_previous_tail"))
    add("j:new-envelope-formula", "Executable formula for the retained recursive envelope", "lean/general",
        "Definitions candidate, familyBound and bound implement the displayed finite maximum; "
        "the two sparse branches select q+1 and q+2 respectively, and all other candidates are zero.",
        lean("RecursiveEnvelope", "candidate", "familyBound", "bound"))
    add("j:new-gains", "Exact recursive improvements over G and the previous envelope", "lean/general",
        "At q=10*2^t the odd/even family gains over G are respectively floor(q/3)-2 and "
        "q/2-floor(q/3)-2. B=G above195; strict improvements hold for both tails t>=5. "
        "At321/322 gains are104/52, and at641/642 they are211/105.",
        lean("BBLFamilyBenchmarks", "odd_baseline_gain", "even_baseline_gain", "strict_previous_tail"))
    add("long:envelope-gains", "Exact gains of the new total envelope on its sparse tail", "lean/derived",
        "Above order 195 the former envelope is G. The family-minus-G equalities and uniqueness "
        "of the matching sparse branch give the displayed exact H-minus-previous values. The "
        "repository proves the family differences and strict-tail comparison directly; no separate "
        "Lean wrapper for every exact H equality is asserted.",
        lean("BBLFamilyBenchmarks", "odd_baseline_gain", "even_baseline_gain", "strict_previous_tail") +
        lean("RecursiveEnvelope", "bound", "strict_previous_tail"))
    add("jup:simple", "Classical simple upper bounds extracted from actual geometry", "lean/general",
        "Every SimpleLowerBound n T obeys 3T<=n(n-2) for n>=2; for even n>=4 it obeys "
        "6T<=n(2n-5). Both conclusions and floor forms are kernel proofs. These formalize "
        "inherited simple-arrangement results, not new unrestricted upper bounds.",
        lean("UpperSimpleOptimality", "simple_lower_bound_upper", "simple_lower_bound_floor") +
        lean("UpperEvenSimpleOptimality", "simple_lower_bound_even_upper", "simple_lower_bound_even_floor"))
    add("j:obstruction", "Exact ten-sign impossibility on the 20-intercept tangent grid", "lean/general",
        "One explicitly listed ten-sign orientation system is impossible for actual tangents "
        "and arbitrary real reciprocal slopes, for every real epsilon. The proof derives the "
        "quartic of tan(pi/20), identifies all required tangent values, and uses positive linear "
        "dependence. It does not classify all perfect21-line arrangements or imply K(21)<=132.",
        lean("BBLGridObstruction", "actual_grid_orientation_impossible", "actual_grid_infeasible") +
        lean("BBLTangentAlgebra", "tan_quartic", "tan_root_interval") +
        lean("StrictLinearCertificate", "infeasible"))
    add("oct:grid21-coverage", "Complete supplied affine-input obstruction audit", "computation + external-input",
        "3765 exact polynomial certificates and15060 reflected/reoriented variants cover236 "
        "supplied Euclidean classes times21 distinguished supports=4956 normalizations, with "
        "no missing cases, for0<epsilon<1/2000000. The checker independently validates signs "
        "and coverage for these inputs. Completeness of Parpalak-Utkin's classification is "
        "an external attributed premise, neither rerun nor formalized in Lean. The earlier18 "
        "projective representatives alone did not establish full affine coverage.",
        artifact("research/three-hour-2026-10-02/constructions/grid21-obstruction/README.md") +
        artifact("research/three-hour-2026-10-02/constructions/grid21-obstruction/affine-verification.json"))
    add("oct:local-robustness", "Ten-sign obstruction persists under small intercept perturbations", "computation",
        "Exact outward interval elimination certifies independent perturbations of radius1/1000 "
        "on the11 used intercepts of the explicit representative. This robustness calculation "
        "is external and is not an all-grid or all-arrangement obstruction.",
        artifact("research/three-hour-2026-10-02/bbl/LOCAL_ROBUSTNESS.md"))
    add("j:exact49", "Uniform49-line compatibility certificate and its proof boundary", "computation + partial",
        "Exact interval checks establish the prescribed49-line rational-slope/actual-tangent "
        "family with767 triangles,47 caps and24 visible pairs throughout0<epsilon<=1/100. "
        "Actual tangent enclosures are Lean theorems. The full finite native base check did "
        "not complete, so the49-line normalized visible seed and its infinite family remain "
        "outside the active library. Target counts768*4^t-1 and768*4^t+24*2^t-1 belong to "
        "a preexisting BBL family; they are not new numerical records.",
        artifact("research/three-hour-2026-10-02/bbl/SEED49_STATUS.md") +
        artifact("research/three-hour-2026-10-02/constructions/uniform-grid49/uniform-seed.json") +
        artifact("research/three-hour-2026-10-02/constructions/uniform-grid49/visibility.json") +
        lean("BBLTangent48Bounds", "tan_48_1_bounds", "tan_48_23_bounds"))
    add("oct:forge33", "Forge-family formulas with the33-line seed still explicit", "lean/conditional-interface",
        "Generic odd/even formulas are proved assuming UniformSeed8 341 and the corresponding "
        "uniform visible seed. The33-line native base check and normalization/visibility drafts "
        "did not complete. Numerical families are attributed to Forge-Ramirez Alfonsin and BBL, "
        "not to the legacy internal source name TamuraSeed33.",
        lean("BBLForgeConditional", "odd_family", "even_family", "odd_polynomial_exact", "even_simple_polynomial_exact") +
        artifact("research/three-hour-2026-10-02/drafts/README.md"))
    add("jup:sharp-fan", "Rigid extremal local fans and the strengthened weighted inequality", "lean/conditional-interface",
        "For a supplied actual cyclic fan, d1=2r-3 forces a full triangular fan and exactly "
        "three core-ended shared rays. Consequently d2<=2 implies d1<=2r-4, and "
        "3d1+d2<=6r-8+2e. Extracting these local interfaces for every core of an arbitrary "
        "arrangement and identifying the global incidences remains unfinished.",
        lean("UpperFan", "Sectors.all_sectors_of_extremal", "Sectors.core_shared_card_eq_three_of_extremal",
             "Sectors.ordinary_shared_card_le_of_core_le_two", "Sectors.weighted_local_bound"))
    add("oct:triple-fan", "Matched extremal triple fans cannot be adjacent", "lean/conditional-interface",
        "Actual full triple fans are incompatible under the explicit shared-edge matching "
        "hypotheses. The canonical global matching and rotation interface remains to be extracted.",
        lean("UpperTripleFan", "extremal_triple_fans_not_adjacent", "incompatible_full_triple_fans"))
    add("oct:core-budget", "Stronger conditional weighted and at-most-three-core budgets", "lean/conditional-interface",
        "Given the displayed aggregate fan bound, actual incidence and charging data imply "
        "2delta>=n+2S-7I+8q-2e+D2. The small-core arithmetic gives delta>=m-6 for q<=3 "
        "and hence T<=floor(m(4m-5)/3)+2. Remaining geometric fan hypotheses prevent these "
        "from being unconditional new nonsimple upper theorems.",
        lean("UpperCoreBudget", "weighted_defect_with_core_edges", "at_most_three_multiple_points",
             "triangles_from_three_core_defect") + lean("UpperCoreLineIncidence", "core_line_budget") +
        lean("UpperCoreCombinatorics", "core_edge_count", "core_surplus"))
    add("oct:next-proof-plan", "Unformalized next-step deductions and research obligations", "research-plan",
        "The degree-three independent exceptional-triple graph idea and inequalities "
        "3e<=D2, 2delta>=n+2S-7I+8q+e and6delta>=3n+6S-21I+24q+D2 are explicitly "
        "prospective deductions under missing global interfaces. They are not current Lean "
        "theorems and do not strengthen a retained exact correction without further information.",
        artifact("research/three-hour-2026-10-02/NEXT_PROOF_PLAN.md"))
    add("oct:searches", "Completed bounded construction searches", "computation",
        "Saved deletion, chord insertion, singular insertion, straightening and grid-fitting "
        "searches produced the exact diagnostics recorded in the construction review, with no "
        "new numerical lower-bound record. Time-limited incumbents, failed fits and fixed-input "
        "obstructions do not establish unrestricted optimality or nonstretchability.",
        artifact("research/three-hour-2026-10-02/constructions/README.md"))
    add("oct:release", "Complete active-source build and trust audit", "verification-metadata",
        "375 active Lean sources,270 build targets and5241 audited theorems:4405 use only "
        "standard logical axioms and836 additionally descend from native evaluation. No active "
        "sorry, admit, unsafe declaration or custom geometric axiom is accepted. These are "
        "implementation audit counts, not discovery counts. Archived March source and October "
        "drafts are outside the active verified library.",
        artifact("verification/lean-summary.json") + artifact("FORMALIZATION.md") +
        artifact("research/three-hour-2026-10-02/RELEASE_VERIFICATION.md"))
    add("long:certificate-definitions", "Coordinate definitions and affine orientation identity", "lean/general",
        "The determinant, oriented vertex evaluation and TrianglePredicate definitions are "
        "formalized, and nonparallel affine intersections satisfy the displayed orientation identity.",
        [reference("Kobon/Geometry.lean", "Kobon."+name) for name in
         ("det", "orientedEval", "TrianglePredicate", "orientedEval_affine")])
    add("lit:classical-upper", "Historical unrestricted upper benchmark", "external",
        "The classical Tamura and Clement-Bader upper comparisons in the literature review "
        "are cited mathematical results. The repository's arithmetic comparisons with their "
        "polynomials do not constitute a formal proof of the unrestricted upper theorem.",
        artifact("paper/references.bib"))
    add("jup:exceptional", "Conditional exceptional-fan correction", "lean/conditional-interface",
        "Given the displayed summed fan premise, the actual incidence/charging/core inequalities "
        "yield2delta>=n+2S-7I+8q+D2-2e. Global extraction of that fan premise is not proved.",
        lean("UpperCoreBudget", "weighted_defect_with_core_edges"))

    # The October index includes all main declarations of every new module.
    # Retain those rows as individually scoped engineering/proof interfaces.
    proof_index = read("research/three-hour-2026-10-02/PROOF_INDEX.md")
    for line in proof_index.splitlines():
        match = re.match(r"\| \[([^]]+)\]\(../../Kobon/([^)]*)\) \| (.*?) \| (.*?) \|$", line)
        if not match:
            continue
        module, filename, declaration_text, scope = match.groups()
        names = re.findall(r"`([^`]+)`", declaration_text)
        refs = lean(module, *names)
        trust = "native" if scope.startswith("**N") else "standard"
        status = "lean/conditional-interface" if any(word in scope.lower() for word in
            ("conditional", "explicit local interface", "explicit matching interface")) else "lean/general"
        add("module:" + module, module + " supporting declarations", status,
            scope.replace("**", "").replace("`", ""), refs, trust=trust,
            role="supporting-declarations")
    add("module:ParametricCached", "Materialized parameter arrays preserve checker soundness", "lean/general",
        "Materializing parameter forms in arrays preserves the exact checker and its soundness. "
        "No measured performance improvement is asserted.",
        lean("ParametricCached", "cache_eq", "simple_sound", "triangle_eq"), trust="standard",
        role="supporting-declarations")

    october_previous = json.loads(read("manuscripts/2026-10-03/shared/proof_map.json"))
    october_claims = {claim["id"]:claim for claim in october_previous["claims"]}
    assert len(october_claims) == 160 and set(october_claims) <= set(claims)
    for identifier, claim in october_claims.items():
        claims[identifier]["previous_edition_status"] = claim["status"]
    extend_claims(add, update, lean, artifact, claims)
    data["previous_october_claim_ids"] = list(october_claims)
    data["previous_october_claims_retained"] = len(october_claims)
    update("oct:release", "verification-metadata",
        f"Current local verification covers {len(summary['source_sha256'])} active sources in "
        f"{summary['mode']} mode, with {audit['theorems']} audited theorems: "
        f"{audit['standard_axioms_only']} standard-only and {audit['native_evaluation_dependent']} "
        "explicit finite-native descendants. Baseline reuse and clean CI are reported separately. "
        "This is implementation provenance, not a count of new mathematical discoveries. "
        f"Local summary complete={summary['complete']}; no passing final CI is inferred from that field.",
        artifact("verification/lean-summary.json")+
        artifact("research/openmath-seven-hour-2026-10-05/RELEASE_VERIFICATION.json"))

    # Retain old identities while giving each a relevant October section.
    for claim in data["claims"]:
        claim["scope"] = re.sub(r"\b(all|for|at|from|above|below|with|and|radius|degree|the|orders|order|lines|line|yields?|implies|throughout|given|supplied|audited)(?=\d)", r"\1 ", claim["scope"])
        claim["scope"] = re.sub(r",(?=\S)", ", ", claim["scope"])
        identifier = claim["id"]
        if identifier.startswith("om:"):
            if identifier in ("om:family37", "om:known-orbits", "om:family61", "om:pareto61", "om:construction-envelope"):
                long_section, short_section = "families", "families"
            elif identifier in ("om:boundary-budget", "om:successor", "om:successor-iteration", "om:perfect-successor"):
                long_section, short_section = "extensions", "extensions"
            elif identifier in ("om:translation-germs", "om:translation-identity", "om:isolated-birth", "om:four-line", "om:six-line"):
                long_section, short_section = "surgery", "certificates"
            elif identifier in ("om:cell41-dual", "om:searches"):
                long_section, short_section = "experiments", "certificates"
            elif identifier == "om:analytic-checkers":
                long_section, short_section = "formalization", "certificates"
            elif identifier == "om:equality-analysis":
                long_section, short_section = "discussion", "upper"
            else:
                long_section, short_section = "upper_bounds", "upper"
        elif identifier in ("j:main", "j:G"):
            long_section, short_section = "introduction", "introduction"
        elif identifier.startswith("jext:"):
            long_section, short_section = "extensions", "extensions"
        elif identifier.startswith("jfam:") or identifier.startswith("module:BBL") or identifier == "oct:forge33":
            long_section, short_section = "families", "families"
        elif identifier == "oct:next-proof-plan":
            long_section, short_section = "discussion", "certificates"
        elif identifier.startswith("jup:") or identifier.startswith("module:Upper") or identifier in ("j:blanc", "oct:core-budget", "oct:triple-fan"):
            long_section, short_section = "upper_bounds", "upper"
        elif identifier == "j:exact49":
            long_section, short_section = "families", "certificates"
        elif identifier in ("j:obstruction", "oct:grid21-coverage", "oct:local-robustness", "oct:searches") or identifier.startswith("module:StrictLinear"):
            long_section, short_section = "experiments", "certificates"
        elif identifier in ("oct:release",) or identifier.startswith("module:Parametric"):
            long_section, short_section = "formalization", "certificates"
        elif identifier.startswith("j:finite") or identifier in ("j:44equality", "j:maiorana-inputs", "j:pu-gallery"):
            long_section, short_section = "finite_results", "certificates"
        elif identifier in ("j:cell", "j:certificate-soundness", "long:certificate-definitions") or identifier.startswith("module:Permutation"):
            long_section, short_section = "geometry", "construction"
        elif identifier in ("j:new-envelope", "j:new-envelope-formula", "j:new-gains", "long:envelope-gains"):
            long_section, short_section = "families", "families"
        else:
            long_section, short_section = "universal", "construction"
        claim["manuscript_sections"] = dict(long="sections/"+long_section+".tex",
                                             journal="sections/"+short_section+".tex")

    data["previous_claim_ids"] = [claim["id"] for claim in previous["claims"]]
    data["previous_claims_retained"] = len(data["previous_claim_ids"])
    all_refs = [ref for claim in data["claims"] for ref in claim["refs"]]
    all_refs += [ref for row in data["finite_catalog"] for ref in row["refs"]]
    files = sorted({ref["path"] for ref in all_refs})
    pinned_files = {}
    for commit in sorted({ref["commit"] for ref in all_refs}):
        selected = sorted({ref["path"] for ref in all_refs if ref["commit"] == commit})
        pinned_files.update(pinned_blobs(selected, commit))
    failures = []
    for path in files:
        current = (ROOT/path).read_bytes()
        pinned = pinned_files[path]
        # Git text attributes may normalize checkout CRLF; provenance uses
        # exact Git content, while also recording the actual checkout hash.
        if current.replace(b"\r\n", b"\n") != pinned.replace(b"\r\n", b"\n"):
            failures.append(path)
        for ref in all_refs:
            if ref["path"] == path:
                ref["checkout_sha256"] = ref["source_sha256"]
                ref["source_sha256"] = hashlib.sha256(pinned).hexdigest()
                ref["git_blob_sha256"] = hashlib.sha256(pinned).hexdigest()
    if failures:
        raise ValueError("Sources differ from pinned Git blobs: " + str(failures))
    data["linked_source_files"] = len(files)
    data["all_sources_match_pinned_git_blobs"] = True
    data["hash_policy"] = "source_sha256 and git_blob_sha256 hash immutable Git blob bytes; checkout_sha256 hashes local bytes. Source equivalence allows CRLF/LF normalization only."
    data["claim_count"] = len(data["claims"])
    (HERE/"proof_map.json").write_text(json.dumps(data, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")

    out = ["# Result-to-proof map for both October manuscripts", "",
           f"Audited 7 October 2026. Mathematical sources are pinned to `{PIN}`; "
           f"verification metadata is pinned to `{VERIFICATION_PIN}`. Every linked revision is explicit in the JSON.", "",
           "This map preserves all **89 historical claim identities**, all **160 October 3 claim identities**, "
           "and **138 finite coordinate identities** (104 simple). It adds the completed quantitative successor, "
           "compatible 33/37/49/61 families, actual degree-free structural bounds and exact translation calculus. "
           "It does not claim every manuscript argument is formalized in Lean.", "",
           "The actual whole-arrangement fan assembly and terminal counting are now complete. The strongest "
           "global all-triple bound retains M22; the strongest component portfolio retains N12 but has no M22 "
           "term. Residual equality analysis and the concrete 41-line dual remain respectively mathematical "
           "analysis and external exact computation.", "",
           "**Trust.** Standard proofs use only `propext`, `Classical.choice`, and `Quot.sound`. "
           "Native descendants additionally trust Lean's compiler/runtime; the ten-dyadic odd/even family "
           "inherits four/six checks, while the61 odd/even seed families inherit five/seven. "
           "A conditional Lean theorem proves its implication, "
           "not automatic satisfaction of every hypothesis. The sign-cell/component interpretation includes "
           "the manuscript's elementary topology argument.", "",
           f"The current [local verification summary](https://github.com/alejandrozu/kobon-proof/blob/{VERIFICATION_PIN}/verification/lean-summary.json) covers "
           f"{data['release_counts']['active_lean_sources']} active Lean sources and audits "
           f"{audit['theorems']} theorem declarations ({audit['standard_axioms_only']} standard-only, "
           f"{audit['native_evaluation_dependent']} finite-native descendants). "
           f"Local mode: `{summary['mode']}`; complete: `{summary['complete']}`. "
           "Unchanged baseline source/import closures are reused. The last confirmed CI listed in the JSON "
           "is identified by its own commit; a successful older run is not attributed to this mathematical pin. "
           "These are audit counts, not mathematical-discovery counts.", "",
           "The [machine-readable map](proof_map.json) binds every declaration line to its source SHA-256 "
           "and immutable Git blob. Rebuild with `python manuscripts/2026-10-07/shared/build_proof_map.py`; "
           "validate without editing with `python manuscripts/2026-10-07/shared/validate_proof_map.py`.", "",
           "## Evidence labels", "",
           "- **lean/general:** the stated proposition for arbitrary permitted parameters, with recorded trust dependencies.",
           "- **lean/finite:** exact finite coordinate certificate, with native evaluation where disclosed.",
           "- **lean/derived:** immediate mathematical corollary of linked complete Lean results; no separate wrapper asserted.",
           "- **lean/conditional-interface:** fully checked implication with explicit geometric or seed premises.",
           "- **partial/manuscript:** a broader ordinary argument includes components not yet formalized.",
           "- **computation:** exact external calculation with its input and parameter scope.",
           "- **external/research-plan:** attributed literature result or explicitly unfinished deduction.", "",
           "## Claim inventory", ""]
    for claim in data["claims"]:
        out += ["### " + claim["id"] + " — " + claim["title"], "",
                f"**Status: {claim['status']}.** {claim['scope']}", ""]
        if claim.get("previous_status") and claim["previous_status"] != claim["status"]:
            out += [f"Previous map status: `{claim['previous_status']}`. The new scope above controls the October claim.", ""]
        for ref in claim["refs"]:
            out += [f"- [{ref['declaration'] or ref['path']}, line {ref['line']}]({ref['url']})"]
        out += [""]
    out += ["## Every retained finite coordinate identity", "",
            "Repeated orders with different coordinate hashes are separate identities. Counts alone do not "
            "establish priority; original input attribution is preserved in the linked certificate and data records.", "",
            "| Order | Triangles | Simple | Coordinate SHA-256 prefix | Lean certificate |", "|---:|---:|:---:|---|---|"]
    for row in data["finite_catalog"]:
        links = "; ".join(f"[{ref['declaration'].split('.')[-1]}]({ref['url']})" for ref in row["refs"])
        out.append(f"| {row['n']} | {row['triangles']} | {'yes' if row['simple'] else 'no'} | `{row['coordinate_sha256'][:16]}` | {links} |")
    (HERE/"proof_map.md").write_text("\n".join(out)+"\n", encoding="utf-8")
    print(json.dumps(dict(claims=len(data["claims"]), previous_claims=89,
        finite_identities=len(data["finite_catalog"]), source_files=len(files), pinned_blob_match=True)))


if __name__ == "__main__":
    generate()
