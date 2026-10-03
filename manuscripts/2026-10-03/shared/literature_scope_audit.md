# Primary-source and novelty audit, 3 October 2026

This short audit supplements the full historical literature review. It
identifies what the current source supports and how it may be used in the
new papers. It does not establish exhaustive worldwide priority.

| Primary source checked | Finding | Consequence for these manuscripts |
|---|---|---|
| [Bartholdi–Blanc–Loisel, 0706.0723v1](https://arxiv.org/html/0706.0723v1), Theorem 1.3, Proposition 3.1, Remark 3.2 | The paper gives affine straight-line families including 6·2^s+1, an explicit doubling construction with gain q², and the small-parameter iteration principle. | Credit the method and numerical family. The proposed 48·2^t+1 branch is its s=t+3 tail. Our advance is the explicit compatibility certificates and closed formal recursive interfaces. |
| [Parpalak–Utkin, 2607.29236v1](https://arxiv.org/abs/2607.29236v1), submitted 31 July 2026 | The paper distinguishes reduced-word enumeration, Euclidean/projective equivalence, exhaustive small-order classification and partial first-hit larger examples. | Keep the affine 236-class input and projective 18-class input separate. Attribute classification completeness. Pseudoline existence alone does not provide a straight-line lower certificate. |
| [Savchuk, 2507.07951v1](https://arxiv.org/abs/2507.07951v1), submitted 10 July 2025 | Exact title: *Constructing Optimal Kobon Triangle Arrangements via Table Encoding, SAT Solving, and Heuristic Straightening*. The work combines table encodings, SAT and straightening. | Use the correct bibliography title. Separate combinatorial feasibility from successful real-line realization; credit imported coordinate inputs. |
| [Georgiev–Gómez-Serrano–Tao–Wagner, 2511.02864v3](https://arxiv.org/abs/2511.02864v3), revised 22 December 2025 | Structured automated search and independently evaluated mathematical constructions offer a methodological comparison. | Cite as methodology where relevant. It is not evidence that this Kobon project or the unrestricted Kobon problem has been solved. |
| [Blanc, 0801.2845](https://arxiv.org/abs/0801.2845) | The simple-arrangement context must be retained when discussing the sharper even upper polynomial. | The new Lean theorem formalizes an inherited upper inequality and cannot be applied to unrestricted multiple-concurrence arrangements. |

The repository's older evidence records remain available. An explicit OEIS
table omission does not establish novelty, and numerical improvements over
the repository's saved envelope do not establish improvements over every
published construction. The current manuscripts claim no new numerical
record from the October session and no unrestricted upper-bound improvement.

The distinctions that most affect correctness are:

1. **All n versus all maxima.** H is a proven construction-based lower bound
   at every natural order. It does not match every best-known individual value.
2. **Infinite family versus arbitrary successor rule.** The compatible seed
   invariants close geometric doubling. They do not prove the March one-line
   recurrence for every starting arrangement or all later successive orders.
3. **Simple versus unrestricted.** Both simple upper polynomials are formal.
   Proposed nonsimple improvements retain the remaining global fan hypotheses.
4. **Exact external versus Lean.** The 236-class obstruction coverage and full
   uniform 49-line seed sign audit are exact external computations. Their
   smaller completed Lean components are linked individually.
5. **Existence versus fixed coordinates.** A family theorem can prove a large
   numerical lower bound while a separate saved coordinate file's independent
   verification remains incomplete.
