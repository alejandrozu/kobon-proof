# Preserved sparse-checker prototype

`OpenMathConstructionSparse.lean` is an unpromoted prototype. Its interval
support-equality arguments passed individually during development, but the
first complete compilation failed on the zero-dimensional default instance
and the noncomputable `Finset.toList` function. Those source issues were
repaired, but the repaired full source was not checked before its production
use was superseded by the parent branch's sparse interval engine.

It is kept outside the active Lean library and release proof claims. The
materialized BooleanMemo checker is the compiled engine used by the complete
33-line seed and the new 61-line seed. Do not treat this prototype as a theorem
in the verified release without first compiling it independently.