import Kobon.BBLPersistence
import Kobon.BBLAssembly
import Kobon.Reindex

/-! Simultaneous retention of old cells in the canonical BBL labels.
Cap replacement is an explicit separate hypothesis; noncap retention is
derived from actual straight-line continuity. -/
namespace Kobon.BBLOldRetention
open Filter BBLPersistence BBLAssembly
open scoped Topology

theorem noncap_eventually (r : Nat) (old D : Nat → Line ℝ)
    (hp : NoParallel (4*r+1) old) (hs : NoConcurrent (4*r+1) old)
    (t : Triple) (ht : TrianglePredicate (4*r+1) old t) (hi : 0 < t.i) :
    ∀ᶠ κ in 𝓝 (0:ℝ), TrianglePredicate (8*r+1)
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) (replace r t) := by
  have hj := ht.1
  have hk := ht.2.1
  have h := triangle_preserved_eventually (4*r+1) (4*r) old D hp hs t ht
    ⟨0,by omega⟩ (by simpa using (ne_of_gt hi).symm) (by dsimp; omega) (by dsimp; omega)
  apply h.mono
  intro κ hκ
  have hh := Reindex.rotate_triangle (8*r+1) (pencilAppend (4*r+1) old D 0 κ) t
    (by convert hκ using 1 <;> omega) hi
  simpa only [replace,if_neg (ne_of_gt hi)] using hh

theorem eventually_list (ts : List Triple) (P : ℝ → Triple → Prop)
    (h : ∀ t∈ts, ∀ᶠ κ in 𝓝 (0:ℝ), P κ t) :
    ∀ᶠ κ in 𝓝 (0:ℝ), ∀ t∈ts, P κ t := by
  induction ts with
  | nil => exact Filter.Eventually.of_forall (by simp)
  | cons a ts ih =>
    have ha := h a (by simp)
    have hb := ih (fun t ht => h t (by simp [ht]))
    filter_upwards [ha,hb] with κ ha hb
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ha
    · exact hb t ht

theorem all_replaced_eventually (r : Nat) (old D : Nat → Line ℝ)
    (hp : NoParallel (4*r+1) old) (hs : NoConcurrent (4*r+1) old)
    (ts : List Triple) (ht : ∀ t∈ts, TrianglePredicate (4*r+1) old t)
    (hcap : ∀ t∈ts, t.i=0 → ∀ᶠ κ in 𝓝 (0:ℝ), TrianglePredicate (8*r+1)
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) (replace r t)) :
    ∀ᶠ κ in 𝓝 (0:ℝ), ∀ t∈ts, TrianglePredicate (8*r+1)
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) (replace r t) := by
  apply eventually_list
  intro t hmem
  by_cases hi : t.i=0
  · exact hcap t hmem hi
  · exact noncap_eventually r old D hp hs t (ht t hmem) (by omega)

theorem all_replaced_positive_eventually (r : Nat) (old D : Nat → Line ℝ)
    (hp : NoParallel (4*r+1) old) (hs : NoConcurrent (4*r+1) old)
    (ts : List Triple) (ht : ∀ t∈ts, TrianglePredicate (4*r+1) old t)
    (hcap : ∀ t∈ts, t.i=0 → ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ → TrianglePredicate (8*r+1)
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) (replace r t)) :
    ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ → ∀ t∈ts, TrianglePredicate (8*r+1)
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) (replace r t) := by
  have hall : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ t∈ts, 0 < κ → TrianglePredicate (8*r+1)
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) (replace r t) := by
    apply eventually_list
    intro t hmem
    by_cases hi : t.i=0
    · exact hcap t hmem hi
    · exact (noncap_eventually r old D hp hs t (ht t hmem) (by omega)).mono
        (fun _ hh _ => hh)
  exact hall.mono (fun _ hh hk t ht => hh t ht hk)

#print axioms all_replaced_positive_eventually
#print axioms noncap_eventually
#print axioms all_replaced_eventually
end Kobon.BBLOldRetention
