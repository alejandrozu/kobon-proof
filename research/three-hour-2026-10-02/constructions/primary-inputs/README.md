# Attributed primary numerical inputs

The files below `data/` are numerical reduced-word arrangements and symmetry
metadata published by **Roman Parpalak and Denis Utkin**, accompanying
[Enumeration and Classification of Triangle-Maximal Pseudoline Arrangements](https://arxiv.org/abs/2607.29236).
They were downloaded from
[parpalak/pseudoline-algorithms](https://github.com/parpalak/pseudoline-algorithms)
at commit `a9c628cbaa765935f224ed5ca5fde7b2f591e16d`.

`manifest.json` gives each original path, pinned raw URL, byte length and
SHA-256. The files are retained unchanged so independent verification can
identify exactly which external mathematical inputs were used. No source
code, manuscript prose, manuscript figures, or LaTeX source was copied.

## Classification scope

The `data/exhaustive/21.uniq-e.txt` file contains 236 representatives of the
published affine Euclidean classes. The smaller `21.uniq-p.txt` file contains
18 projective representatives for the 22-support closures including the line
at infinity. Those 18 chosen affine representatives alone do not cover every
affine type. The final obstruction audit uses the 236-class file and checks
all 21 possible distinguished supports in each affine class.

The completeness of the published classification remains an attributed
external theorem. Our verifier independently checks the encoded arrangements,
their triangle counts, the chosen normalizations, and the algebraic obstruction
certificates; it does not rerun the authors' exhaustive enumeration.

Larger files under `data/partial/` are first-hit **pseudoline** examples.
They are not straight-line realizations and are never counted as classical
Kobon lower bounds here.

## Licensing information found at the pinned commit

A recursive repository-tree inspection on 2 October 2026 found no root
`LICENSE` and no data-directory license. The only license file found was
[`preprint/LICENSE`](https://github.com/parpalak/pseudoline-algorithms/blob/a9c628cbaa765935f224ed5ca5fde7b2f591e16d/preprint/LICENSE).
It reserves the rights in the manuscript material and describes source code
elsewhere as MIT-licensed. It does not explicitly license the numerical
enumeration files. We therefore record their data license as **not explicitly
specified in the inspected commit**, preserve the authors' attribution, and
do not relabel these external inputs as our own work or as MIT-licensed data.

The source's
[`data/README.md`](https://github.com/parpalak/pseudoline-algorithms/blob/a9c628cbaa765935f224ed5ca5fde7b2f591e16d/data/README.md)
documents the reduced-word encoding and distinguishes exhaustive data from
partial first-hit examples. That document is linked rather than copied.
