# A fully formalized tangent-grid obstruction

Checked on 2026-10-02 with the repository's pinned Lean 4.31.0 toolchain.
The final theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
There are no finite native checks or unproved mathematical axioms in this
proof chain.

## Exact statement

Let `t = tan(pi/20)` and write `T_k = tan(k*pi/20)`. For any real epsilon,
put the twenty intercepts in the order

`a = (-T_9,...,-T_1,-epsilon,+epsilon,T_1,...,T_9)`.

For arbitrary real reciprocal slopes `v_i`, define the actual straight lines
`L_i: x-v_i*y=a_i`. Set

`D(i,j,k)=(a_j-a_k)*v_i+(a_k-a_i)*v_j+(a_i-a_j)*v_k`.

The following ten strict inequalities cannot all hold:

| Triple `(i,j,k)` | Required sign of `D(i,j,k)` |
|---|---:|
| (0,6,15) | negative |
| (0,7,13) | positive |
| (0,8,14) | negative |
| (0,13,19) | positive |
| (3,6,8) | positive |
| (3,11,15) | negative |
| (3,13,17) | positive |
| (7,11,13) | positive |
| (8,14,17) | negative |
| (8,15,19) | negative |

This is `Kobon.BBLGridObstruction.actual_grid_orientation_impossible`.
The Lean `evalVertex L_k L_i L_j` is proved equal to the displayed `D`.
The intercepts are the actual `BBLCrossingCoordinates.oldIntercept 5 epsilon`,
not an approximate grid or a separately assumed algebraic model.

Neither epsilon nor the reciprocal slopes need to be small, bounded, or
continuous. In particular, allowing slopes to diverge as epsilon tends to
zero cannot circumvent these ten constraints. The two epsilon-dependent
intercepts do not occur in this particular certificate.

## Proof

`BBLTangentAlgebra.tan_quartic` proves

`Q(t)=t^4-4*t^3-14*t^2-4*t+1=0`.

Its `real_root_characterization` identifies `tan(pi/20)` as the unique root
of this polynomial in `(3/20,17/100)`. The proof uses exact trigonometric
identities and rational bounds already present in the repository.

`BBLTangentValues.value_eq_tan` proves exact cubic expressions for all nine
`T_k`. For example,

`T_2=(-3*t^3+14*t^2+31*t-2)/10`,

`T_3=(-2*t^3+9*t^2+24*t-3)/2`,

`T_9=-t^3+4*t^2+14*t+4`.

The ten positive weights, in the table's order, are

```
-20*t^3 +120*t^2 +300*t -40
 -8*t^3  +24*t^2  +96*t  +8
-45*t^3 +205*t^2 +555*t -35
-16*t^3   -6*t^2  +40*t  +2
 20*t^3 -100*t^2 -220*t +100
 20*t^3 -120*t^2 -220*t +200
 20*t^3 -150*t^2 -300*t +130
-60*t^3 +240*t^2 +860*t +320
-105*t^3+455*t^2+1275*t -45
 36*t^3 -188*t^2 -452*t +124
```

Lean verifies positivity on the whole isolating interval. It also verifies
that every column of the weighted signed coefficient matrix is zero:
each unreduced column is explicitly a polynomial multiple of `Q(t)`.
The generic `StrictLinearCertificate.homogeneous_infeasible` theorem then
gives the contradiction between a positive weighted sum and zero.

## Provenance and limits

The exact search found this as representative238, class_index11,
distinguished support13, shift0. The source data are
`research/three-hour-2026-10-02/constructions/grid21-obstruction/representative-238.json`.
The Lean theorem embeds the ten signs and weights explicitly; it does not
assume the JSON, the numerical search, or the classification code is correct.

The initial broader computer-assisted audit checked 366 systems arising from
7,560 normalized charts of eighteen supplied 21-support configurations.
Those inputs represent projective classes and do not exhaust the affine
cases. The completed correction uses all 236 supplied Euclidean classes:
3,765 exact polynomial certificates cover all 4,956 class/distinguished-line
choices for `0 < epsilon < 1/2000000`, with no missing case. The
[full exact audit](../constructions/grid21-obstruction/affine-verification.json)
records the checks. Completeness of the external classification remains
attributed to Parpalak–Utkin. This wider computer-assisted result does not
change the present Lean theorem's exact ten-sign scope.

It is not a general upper bound for the Kobon problem, not a proof that
optimal21-line arrangements do not exist, and not a proof that every possible
optimal21-line arrangement fails every generalized doubling construction.

## Reproduction

- `generate_tangent_values.py` emits `Kobon/BBLTangentValues.lean`.
- `generate_grid_obstruction.py` emits `Kobon/BBLGridObstruction.lean`.
- Both generators read the exact representative JSON; the generated Lean
  proofs independently check every identity in the real numbers.
- `tangent-algebra-axioms.log`, `tangent-values-axioms.log`, and
  `grid-obstruction-axioms.log` preserve the successful compiler output.

The completed obstruction check took about five minutes on this host with
one Lean thread. Most of the file consists of finite kernel-checked algebra
and coordinate substitutions; it requires no external solver at check time.
