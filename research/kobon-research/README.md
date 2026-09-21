# Kobon construction research — 20 September 2026

**Outcome:** an explicit additional-line construction and a proof argument for

\[
K(N_t)\ge N_t(N_t-3)/3+1,\qquad N_t=6\,2^t+3.
\]

This is a **derived corollary of the Parpalak–Utkin even construction**, which
itself uses Bartholdi–Blanc–Loisel doubling. It is not an independently invented
seed family. **Novelty and improvement over all previously known lower bounds
have not been established.** The requested new record family for even numbers
of lines has not been obtained in this research pass.

The proof argument is in [proof_note.md](proof_note.md). It uses ordinary
mathematical reasoning and cited results; it is not a Lean formalization.
The stored examples are unconditional finite certificates: their rational
coordinates and counts can be checked without trusting either paper.

| Lines | Certified triangles | Formula |
|---:|---:|---:|
| 51 | 817 | 817 |
| 99 | 3,169 | 3,169 |
| 195 | 12,481 | 12,481 |

The smaller members have 9, 15, and 27 lines and give 19, 61, and 217 triangles.
These are **below** the known records 21, 65, and 225. Thus an infinite formula
must not be presented as evidence that every member is a record.

## Reproduce the finite verification

Python 3 standard library only:

```text
python verify_direct.py certificates/n051.json certificates/n099.json certificates/n195.json
```

`verify_direct.py` examines every triple of lines, rejects zero-area triples,
and checks that no other line meets the open interior. It uses integer
homogeneous coordinates throughout the count. The construction was also
counted by a separately implemented method using consecutive vertices along
each side; see `exact_geometry.py`.

To propose a new rational instance (requires `mpmath`):

```text
python generate.py 3 certificates/new-n051.json
python verify_direct.py certificates/new-n051.json
```

Generation approximates the algebraic/trigonometric parameters with rationals
and preserves the two triple points exactly. It checks the resulting finite
arrangement. A chosen numeric precision is **not** a proof for every parameter
value; the infinite argument is separate in the proof note.

## What the research tested

- Independently reproduced the public 20-, 26-, 32-, 38-, and 50-line
  certificates with counts 117, 204, 315, 450, and 792.
- Tested the 20-, 32-, and 38-line configurations against selected tangent-grid
  normalizations needed for repeated doubling. No successful seed was obtained.
  These restricted searches do not prove that other normalizations are impossible.
- Examined 43,729 and 104,334 distinct dual boundary vertices when varying the
  affine chart of the fixed 26- and 32-line certificates. No improvement over
  204 and 315 was found by that implementation. This is not a universal upper
  bound over all arrangements.
- Tested all pairs of deletions from the public 26- and 50-line certificates.
  The best remaining counts were 169 on 24 lines and 715 on 48 lines.
- Tested 4,095 selected one- or two-triangle collapses of a rational approximation
  to the published iterative 19-line seed. 867 candidates passed exact sign
  checks. Their best even extension by a line beyond every vertex had 115
  triangles, below the current 20-line record of 117.
- Reconstructed the published even construction and extended it by a line
  outside all existing vertices in a specified direction. This produced the
  family discussed in the proof note.

The failed searches are recorded to avoid repeating them. They are evidence
about the tested routes, not impossibility results for a new infinite family.

## Sources and attribution

- [Parpalak–Utkin, even construction draft](https://github.com/parpalak/kobon-even-draft/blob/master/8-14-26-even-series.md).
- [Bartholdi–Blanc–Loisel, 2007 preprint](https://arxiv.org/abs/0706.0723).
- [Parpalak–Utkin, iterative 19-line seed](https://github.com/parpalak/triangle-maximal-18-series).
- [Public exact record certificates](https://github.com/ud1/kobon-solutions/tree/master/gallery/certificates).
- [OEIS A006066](https://oeis.org/A006066).
- [Zarzuelo Urdiales, earlier paper](https://archivara.org/paper/48b411c9-0e03-4592-931e-179b9a1c2312).

No OEIS edits, publication submissions, or messages to other researchers were made.
