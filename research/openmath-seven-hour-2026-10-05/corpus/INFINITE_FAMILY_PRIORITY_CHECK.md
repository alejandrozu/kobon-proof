# Bounded primary-source comparison for the 60-dyadic orbit

Checked 6 October 2026. This is a source comparison, not an exhaustive
historical-priority certificate.

The completed family starts with a uniform 61-line arrangement carrying 1190
triangles and 59 distinguished-line caps. Classical doubling gives

```
q_t=60*2^t,
T_t=1200*4^t-10,
n_t=q_t+1.
```

The odd simple upper bound is `1200*4^t-1`, so the candidate deficit is9
at every depth. The point count 1190 and its source arrangement belong to
Rohith Poola. The rational-slope refit preserves 1190 throughout a positive
epsilon interval and has now been connected to the proved geometric
recursion in Lean. A further cap-cone mutation certifies 29 visible pairs
instead of 28. The resulting even formula is
`1200*4^t+30*2^t−11`, at `60*2^t+2` lines, one stronger than the earlier
28-pair family at every depth. The compatible seed and unconditional odd/even
families have passed their full proof pipelines. The whole-project release
audit is tracked separately under `verification/`.

Relevant inspected primary sources:

- [Bartholdi--Blanc--Loisel, arXiv0706.0723v1](https://arxiv.org/html/0706.0723v1),
  Theorem1.3 and Proposition3.1: straight optimal orbits based on6 and14,
  with the18 orbit then established for pseudolines; the doubling method
  and iteration requirement are prior research.
- [Parpalak--Utkin, arXiv2604.22035v1](https://arxiv.org/html/2604.22035v1),
  Sections1 and5: the18 orbit is now straight-line. Their introduction also
  lists the prior power-of-two orbit of Forge--Ramírez Alfonsín. Section6
  tests optimal21/23/27 compatibility and gives no base there; AppendixB
  gives one-step41/45/49 examples.
- [Savchuk, arXiv2507.07951v1](https://arxiv.org/html/2507.07951v1),
  finite constructions at23/24/27 and a table/SAT/straightening framework.
- [Parpalak--Utkin, arXiv2607.29236v1](https://arxiv.org/html/2607.29236v1):
  a large combinatorial pseudoline classification. Such results do not by
  themselves certify straight-line realizations of a doubled optimum.

No60-dyadic straight-line1190/4790 family was located in these inspected
sources. That observation supports a distinct-family comparison, while
stronger unpublished straight constructions or another literature source
could change priority. A perfect31-line pseudoline construction and a
general combinatorial doubling must not be substituted for a compatible
straight-line31-line seed.

The separately formalized 37-line seed gives the already known numerical
18-dyadic straight orbit starting at its next depth. Its exact compatible
certificate and universal-successor linkage are formalization contributions;
its counts are not presented as a new numerical family.

A refreshed bounded web search on 6 October used the queries “site:arxiv.org
Kobon triangles September October 2026 upper bound” and “site:oeis.org
A006066 Kobon 2026”. The returned
[OEIS internal record](https://oeis.org/A006066/internal) was dated 28 September
2026. This search did not establish an additional accepted all-order solution;
search absence is not a proof of nonexistence or historical priority. Recent
preprint upper-bound claims are assessed through their actual dependencies
and exact counterexamples in the separate corpus audit, not accepted solely
from their abstracts.
