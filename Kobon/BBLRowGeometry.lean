import Kobon.BBLCount

/-! Geometric soundness of the explicit BBL crossing-order model.
The hypothesis is a monotone order of actual intersection coordinates,
not a triangle-count hypothesis. Analytic realization is a separate module.
-/
namespace Kobon.BBLRowGeometry
open Finset Exterior BBLRowOrder BBLCount BBLTriangles
set_option maxHeartbeats 10000000

def crossKey (r i label : Nat) : Int :=
  if label<4*r then oldKey label else newKey (2*r) i (label-4*r)

def CrossingOrder (r : Nat) (L : Nat → Line ℝ) (w : Line ℝ) : Prop :=
  ∀ i : Nat, i≤4*r → ∀ a b : Fin (8*r+1),
    a.val≠4*r+i → b.val≠4*r+i → crossKey r i a≤crossKey r i b →
      projection w (intersection (L (4*r+i)) (L a))≤
      projection w (intersection (L (4*r+i)) (L b))

theorem row_outside (r : Nat) (hr : 1≤r) (L : Nat → Line ℝ) (w : Line ℝ)
    (horder : CrossingOrder r L w) (i k j : Nat)
    (hi : i≤4*r) (hk : k≤4*r) (hik : i≠k) (hj : j<4*r)
    (hclose : |newKey (2*r) i k-oldKey j|<4)
    (s : Fin (8*r+1)) (hsi : s.val≠4*r+i) :
    Outside (projection w (intersection (L (4*r+i)) (L s)))
      (projection w (intersection (L (4*r+i)) (L (4*r+k))))
      (projection w (intersection (L (4*r+i)) (L j))) := by
  have hside :
      (crossKey r i s≤newKey (2*r) i k ∧ crossKey r i s≤oldKey j) ∨
      (newKey (2*r) i k≤crossKey r i s ∧ oldKey j≤crossKey r i s) := by
    by_cases hs : s.val<4*r
    · simp only [crossKey,if_pos hs]
      by_cases he : s.val=j
      · rw [he]
        rcases le_total (oldKey j) (newKey (2*r) i k) with h | h
        · exact Or.inl ⟨h,le_rfl⟩
        · exact Or.inr ⟨h,le_rfl⟩
      · exact old_outside_of_close (2*r) i k j s (by exact_mod_cast Ne.symm he) hclose
    · simp only [crossKey,if_neg hs]
      exact auxiliary_outside_of_close (2*r) i k (s.val-4*r) j (by omega)
        (by omega) (by omega) (by omega) (by omega) (by exact_mod_cast hik)
        (by omega) (by omega) (by omega) (by omega) (by omega) hclose
  let a : Fin (8*r+1) := ⟨4*r+k,by omega⟩
  let b : Fin (8*r+1) := ⟨j,by omega⟩
  have ha : a.val≠4*r+i := by dsimp [a]; omega
  have hb : b.val≠4*r+i := by dsimp [b]; omega
  have hka : crossKey r i a=newKey (2*r) i k := by
    dsimp [crossKey,a]
    rw [if_neg (by omega)]
    congr 1 <;> omega
  have hkb : crossKey r i b=oldKey j := by simp [crossKey,b,hj]
  rcases hside with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨horder i hi s a hsi ha (by simpa only [hka] using h1),
      horder i hi s b hsi hb (by simpa only [hkb] using h2)⟩
  · exact Or.inr ⟨horder i hi a s ha hsi (by simpa only [hka] using h1),
      horder i hi b s hb hsi (by simpa only [hkb] using h2)⟩

def mixedTriangle (r : Nat) (t : Nat × Nat × Nat) : Triple :=
  ⟨t.2.2,4*r+t.1,4*r+t.2.1⟩

theorem mixed_triangle (r : Nat) (hr : 1≤r) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (t : Nat × Nat × Nat) (ht : t∈mixed r) :
    TrianglePredicate (8*r+1) L (mixedTriangle r t) := by
  rcases t with ⟨i,k,j⟩
  rcases (mem_mixed _ _ _ _).mp ht with ⟨hik,hk,hj,hclose⟩
  have hi : i≤4*r := by omega
  have hswap : newKey (2*r) k i=newKey (2*r) i k := by
    exact newKey_symm (2*r) k i (by omega) (by omega) (by omega) (by omega) (by omega)
  have hclose' : |newKey (2*r) k i-oldKey j|<4 := by simpa only [hswap] using hclose
  apply triangle_of_last_two_sides (8*r+1) L w hp hs hw (mixedTriangle r (i,k,j))
    (by dsimp [mixedTriangle]; omega) (by dsimp [mixedTriangle]; omega)
    (by dsimp [mixedTriangle]; omega)
  · intro s hsi
    have hh := row_outside r hr L w horder i k j hi hk (by omega) hj hclose s hsi
    dsimp [mixedTriangle]
    simpa only [intersection_swap (L j) (L (4*r+i))] using hh
  · intro s hsk
    have hh := row_outside r hr L w horder k i j hk hi (by omega) hj hclose' s hsk
    dsimp [mixedTriangle]
    simpa only [intersection_swap (L (4*r+i)) (L (4*r+k)),
      intersection_swap (L j) (L (4*r+k))] using hh

theorem mixedTriangle_injective (r : Nat) : Function.Injective (mixedTriangle r) := by
  rintro ⟨i,k,j⟩ ⟨a,b,c⟩ he
  have h1 := congrArg Triple.i he
  have h2 := congrArg Triple.j he
  have h3 := congrArg Triple.k he
  dsimp [mixedTriangle] at h1 h2 h3
  have : i=a := by omega
  have : k=b := by omega
  subst a; subst b; subst c
  rfl

theorem mixed_witness (r : Nat) (hr : 1≤r) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w) :
    ∃ ts : List Triple, ts.Nodup ∧
      (∀ t∈ts, TrianglePredicate (8*r+1) L t ∧ 4*r≤t.j) ∧
      (4*r)^2≤ts.length := by
  classical
  let s := (mixed r).image (mixedTriangle r)
  refine ⟨s.toList,Finset.nodup_toList _,?_,?_⟩
  · intro t ht
    obtain ⟨p,hp',rfl⟩ := mem_image.mp (Finset.mem_toList.mp ht)
    exact ⟨mixed_triangle r hr L w hp hs hw horder p hp',by dsimp [mixedTriangle]; omega⟩
  · dsimp [s]
    rw [Finset.length_toList,card_image_of_injective _ (mixedTriangle_injective r)]
    exact mixed_count r hr

#print axioms mixed_triangle
#print axioms mixed_witness
end Kobon.BBLRowGeometry
