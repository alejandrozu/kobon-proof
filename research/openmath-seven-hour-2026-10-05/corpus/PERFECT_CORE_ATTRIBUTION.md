# Perfect arrangements and the new degree-two core proof

Primary-source and corpus check, 6 October 2026.

Clément and Bader's2007 unpublished note
[Tighter Upper Bound for the Number of Kobon Triangles](https://oeis.org/A006066/a006066.pdf)
already states, in Lemma1 and the Lemma2 proof, that exact Tamura equality
forces a perfect configuration with only ordinary crossings. These are on
PDF pages1–2 after the title page, web text locators91–129. Therefore the
broad conclusion “zero Tamura deficit implies simplicity” is a prior stated
claim, rather than a newly proposed conclusion.

Their shared-side accounting also asserts that each multiple point belongs
to at most two shared-side pairs. The independently reconstructed phase-zero
FP witnesses in this corpus violate that auxiliary restriction; for example,
the8-line arrangement has14 triangles and15 shared sides, with7 triple points.
The per-core incidence profile contains more than two shared sides at a core.
This obstruction invalidates importing that particular counting argument as
our verified proof. It does not by itself disprove the claimed upper bound or
the claimed equality characterization.

The upper branch's new result uses actual shared-core graph degree at most2.
Under zero deficit, actual local rigidity yields triple cores with two
ordinary-shared and two core-shared rays. Matching their certified triangles
forces3-cycles, and normalized fan geometry prevents such a cycle from
closing. The closed-component strictness is therefore an independent proved
mechanism in an explicit restricted scope. Its standard-axiom Lean proof is
assessed through the upper branch's completed build logs.

For contestant attribution, the pinned Raj notes
`work/openmath-raj/proofs/all8/ALL8_NOTE7.md` and `ALL8_NOTE8.md` prove useful
component capacities and the wrong-ray two-four-run bridge obstruction.
Note7 explicitly leaves larger components with five-/six-sector triples open;
Note8 treats one exceptional five-run vertex with opposite-four partners.
No exact all-five-run3-cycle or arbitrary degree-two perfect-core closure
was located in those notes. The shared-ray mechanism should be credited to
the relevant earlier local arguments while the new exact scope and proof are
described separately.
