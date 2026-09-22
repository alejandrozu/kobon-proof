# Independent review of Maiorana's fourteen-line constructions

On 22 September 2026 we independently checked all fifteen rational configurations published by **Andrea Maiorana**, who reports finding them on 11–12 August 2026. These are Maiorana's constructions, not new constructions by Zarzuelo or this research session.

Source: [rufio72/kobon_triangles_k14](https://github.com/rufio72/kobon_triangles_k14), immutable commit `e47c7cfd9661e54d29befb83118bf83d5f804028`, committed `2026-08-12T13:28:03Z`. The source data, documentation and code are licensed **CC BY 4.0**; the original LICENSE and README are retained here. Original coordinate files are `sol01.json` through `sol15.json`. Our added certificate wrappers are `certificate-01.json` through `certificate-15.json` and preserve attribution and immutable source links. Changes consist of adding the line count, triangle count, independently enumerated triangle list and verification metadata.

All fifteen configurations have exactly **54 positive-area bounded triangular faces**, with **no parallel pairs**. Fourteen have precisely two triple points; solution 11 has four triple points. There are no points of higher multiplicity. We verified these facts with our pre-existing exact elementary-segment adjacency counter and separately with our pre-existing exact open-interior sign counter. We did not execute the source repository's verification programs. The full side-use and multiplicity census appears in `verification.json`.

The discovery establishes the lower bound `K(14) >= 54`. Our independent recount establishes the validity of these submitted coordinates. The author's assertion that a published upper bound proves unrestricted optimality is **not imported here**: the classical upper-bound scope audit remains separate. Our paper-level theorem for even pairwise nonparallel arrangements with at most two finite multiple points gives upper54 at14, so fourteen of these witnesses attain that restricted theorem. That geometric upper theorem is not fully formalized in Lean.

## A complete local smoothing obstruction

Solution1 has triple points supported by lines `{0,4,10}` and `{0,11,12}`. Offset lines4 and11 independently by `+1/1000` or `-1/1000`, leaving their normals and all other lines unchanged. Exact determinant arithmetic verifies that every originally nonzero determinant retains its sign. The two formerly zero determinants independently realize all four choices of sign. The exact face counts are:

| Offset of line4 | Offset of line11 | Surviving old triangles | New tiny triangles | Total |
|---:|---:|---:|---:|---:|
| -1/1000 | -1/1000 | 50 | 2 | 52 |
| -1/1000 | +1/1000 | 50 | 2 | 52 |
| +1/1000 | -1/1000 | 51 | 2 | 53 |
| +1/1000 | +1/1000 | 50 | 2 | 52 |

The four exact certificates and complete changed-face lists are recorded in `resolutions.json`. The combinatorial type of a sufficiently small simple perturbation is determined by the unchanged signs and these two resolution signs. Thus every such perturbation has at most53 triangular faces. This is a direct obstruction to the proposed nondecreasing smoothing strategy, even when every local resolution choice is independently realizable by straight lines. The relaxed MaxSAT objective “one new triangle per triple point plus surviving old triangles” has maximum53, below the original54.

The finite determinant/sign census and coordinate checks are exact executable mathematics. The continuity argument identifying all sufficiently small perturbations is a mathematical explanation, not yet a Lean theorem. The independent discovery and documentation of this obstruction do not imply numerical priority for the underlying construction.

## Reproduction

From the repository root, using Python3's standard library:

```text
python experiments/2026-09-21/general-bounds/check_maiorana14.py
python research/kobon-extension/verify_direct.py research/six-hour-2026-09-21/general-bounds/maiorana14/certificate-01.json
python experiments/2026-09-21/general-bounds/maiorana_resolutions.py
```

The first command downloads immutable coordinate data and repeats all fifteen adjacency/side-use audits. The second command illustrates the separate interior-sign check, which was run on all fifteen certificates during this session. The third exhausts the four local resolution types and repeats both counts on them.
