import Kobon.BBLPersistence

/-! Saturated consecutive segments on a distinguished line force the old
triangular apices to alternate sides. This is a geometric input for replacing
the old distinguished triangles by the interleaved BBL pencil. -/
namespace Kobon.BBLAlternation
open BBLExtrema BBLTriangles BBLPersistence Exterior

theorem product_pos_of_weak {x y z : ℝ} (h : weakSigns x y z)
    (hx : x ≠ 0) (hz : z ≠ 0) : 0 < x*z := by
  rcases h with h | h
  · exact mul_pos (lt_of_le_of_ne h.1 (Ne.symm hx))
      (lt_of_le_of_ne h.2.2 (Ne.symm hz))
  · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne h.1 hx)
      (lt_of_le_of_ne h.2.2 hz)

theorem graph_height (m a s b : ℝ) (hms : m ≠ s) :
    (intersection (graphLine m a) (graphLine s b)).2 =
      m*s*(b-a)/(s-m) := by
  dsimp [intersection,vertex,graphLine,det]
  rw [show m*(-1)-(-1)*s=s-m by ring]
  congr 1
  ring

theorem oriented_base (m a s b : ℝ) :
    orientedEval (graphLine m a) (graphLine 0 0) (graphLine s b) =
      m*s^2*(b-a) := by
  dsimp [orientedEval,evalVertex,vertex,graphLine,det]
  ring

theorem det_graph (m a s b : ℝ) : det (graphLine m a) (graphLine s b)=s-m := by
  dsimp [det,graphLine]
  ring

/-- The four-line algebraic core, using the actual emptiness signs at both
consecutive triangles. The same nonzero cyclic determinant occurs in both. -/
theorem alternating_algebra (A B C a b c E : ℝ)
    (hab : a<b) (hbc : b<c) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (hAB : A≠B) (hBC : B≠C) (hE : E≠0)
    (hleft : weakSigns (C*A^2*(a-c)) (C*B^2*(b-c)) (E*(B-A)))
    (hright : weakSigns (A*B^2*(b-a)) (A*C^2*(c-a)) (E*(C-B))) :
    (A*B*(b-a)/(B-A))*(B*C*(c-b)/(C-B)) < 0 := by
  have hdAB : B-A≠0 := sub_ne_zero.mpr (Ne.symm hAB)
  have hdBC : C-B≠0 := sub_ne_zero.mpr (Ne.symm hBC)
  have hac : a<c := lt_trans hab hbc
  have hleft' := product_pos_of_weak hleft
    (mul_ne_zero (mul_ne_zero hC (pow_ne_zero _ hA)) (sub_ne_zero.mpr (ne_of_lt hac)))
    (mul_ne_zero hE hdAB)
  have hright' := product_pos_of_weak hright
    (mul_ne_zero (mul_ne_zero hA (pow_ne_zero _ hB)) (sub_ne_zero.mpr (ne_of_gt hab)))
    (mul_ne_zero hE hdBC)
  have hfac : A^2*(a-c)<0 := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hA) (sub_neg.mpr hac)
  have hfac' : 0<B^2*(b-a) := mul_pos (sq_pos_of_ne_zero hB) (sub_pos.mpr hab)
  have hl : C*E*(B-A)<0 := by
    have heq : (C*A^2*(a-c))*(E*(B-A)) = (A^2*(a-c))*(C*E*(B-A)) := by ring
    rw [heq] at hleft'
    nlinarith
  have hr : 0<A*E*(C-B) := by
    have heq : (A*B^2*(b-a))*(E*(C-B)) = (B^2*(b-a))*(A*E*(C-B)) := by ring
    rw [heq] at hright'
    nlinarith
  have hprod := mul_neg_of_neg_of_pos hl hr
  have heq : (C*E*(B-A))*(A*E*(C-B)) = (A*C*(B-A)*(C-B))*E^2 := by ring
  rw [heq] at hprod
  have hcore : A*C*(B-A)*(C-B)<0 := by
    have he2 := sq_pos_of_ne_zero hE
    nlinarith
  have hscale : 0<B^2*(b-a)*(c-b)/((B-A)*(C-B))^2 :=
    div_pos (mul_pos (mul_pos (sq_pos_of_ne_zero hB) (sub_pos.mpr hab)) (sub_pos.mpr hbc))
      (sq_pos_of_ne_zero (mul_ne_zero hdAB hdBC))
  have heq' : (A*B*(b-a)/(B-A))*(B*C*(c-b)/(C-B)) =
      (A*C*(B-A)*(C-B))*(B^2*(b-a)*(c-b)/((B-A)*(C-B))^2) := by
    field_simp
    <;> ring
  rw [heq']
  exact mul_neg_of_neg_of_pos hcore hscale

/-- Two consecutive certified triangular cells above a saturated old line
have apices on opposite sides of that line. No desired sign is assumed. -/
theorem consecutive_apices (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L)
    (i j k : Nat) (hi : 0 < i) (hij : i < j) (hjk : j < k) (hkn : k < n)
    (A B C a b c : ℝ) (hab : a<b) (hbc : b<c)
    (h0 : L 0=graphLine 0 0) (hA : L i=graphLine A a)
    (hB : L j=graphLine B b) (hC : L k=graphLine C c)
    (hleft : TrianglePredicate n L ⟨0,i,j⟩)
    (hright : TrianglePredicate n L ⟨0,j,k⟩) :
    (intersection (L i) (L j)).2*(intersection (L j) (L k)).2 < 0 := by
  have hin : i<n := by omega
  have hjn : j<n := by omega
  have hzn : 0<n := by omega
  have hAn : A≠0 := by simpa [h0,hA,graphLine,det] using hp ⟨0,hzn⟩ ⟨i,hin⟩ hi
  have hBn : B≠0 := by simpa [h0,hB,graphLine,det] using hp ⟨0,hzn⟩ ⟨j,hjn⟩ (show 0<j by omega)
  have hCn : C≠0 := by simpa [h0,hC,graphLine,det] using hp ⟨0,hzn⟩ ⟨k,hkn⟩ (show 0<k by omega)
  have hAB : A≠B := by
    have hh := hp ⟨i,hin⟩ ⟨j,hjn⟩ hij
    intro heq
    simp [hA,hB,graphLine,det,heq] at hh
  have hBC : B≠C := by
    have hh := hp ⟨j,hjn⟩ ⟨k,hkn⟩ hjk
    intro heq
    simp [hB,hC,graphLine,det,heq] at hh
  let E := evalVertex (L k) (L i) (L j)
  have hE : E≠0 := hs ⟨i,hin⟩ ⟨j,hjn⟩ ⟨k,hkn⟩ hij hjk
  have hl := hleft.2.2.2.2 ⟨k,hkn⟩
  have hr := hright.2.2.2.2 ⟨i,hin⟩
  have hl' : weakSigns (C*A^2*(a-c)) (C*B^2*(b-c)) (E*(B-A)) := by
    have he : orientedEval (L k) (L i) (L j)=E*(B-A) := by
      change E*det (L i) (L j)=_
      rw [hA,hB,det_graph]
    change weakSigns (orientedEval (L k) (L 0) (L i))
      (orientedEval (L k) (L 0) (L j)) (orientedEval (L k) (L i) (L j)) at hl
    rw [he,h0,hA,hB,hC,oriented_base,oriented_base] at hl
    exact hl
  have hr' : weakSigns (A*B^2*(b-a)) (A*C^2*(c-a)) (E*(C-B)) := by
    have he : evalVertex (L i) (L j) (L k)=E := by
      exact eval_cyclic _ _ _
    have he' : orientedEval (L i) (L j) (L k)=E*(C-B) := by
      rw [orientedEval,he,hB,hC,det_graph]
    change weakSigns (orientedEval (L i) (L 0) (L j))
      (orientedEval (L i) (L 0) (L k)) (orientedEval (L i) (L j) (L k)) at hr
    rw [he',h0,hA,hB,hC,oriented_base,oriented_base] at hr
    exact hr
  rw [hA,hB,hC,graph_height A a B b hAB,graph_height B b C c hBC]
  exact alternating_algebra A B C a b c E hab hbc hAn hBn hCn hAB hBC hE hl' hr'

theorem signs_from_negative (N : Nat) (h : Nat → ℝ) (hzero : h 0<0)
    (hstep : ∀ j, j+1<N → h j*h (j+1)<0) :
    ∀ j, j<N → (j%2=0 → h j<0) ∧ (j%2=1 → 0<h j) := by
  intro j
  induction j with
  | zero =>
      intro _
      exact ⟨fun _ => hzero,by omega⟩
  | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hp := hstep j hj
      constructor
      · intro he
        have hjodd : j%2=1 := by omega
        have hh := hi.2 hjodd
        nlinarith
      · intro ho
        have hjeven : j%2=0 := by omega
        have hh := hi.1 hjeven
        nlinarith

/-- A positive apex at an odd central gap determines every sign in the chain. -/
theorem signs_from_odd_center (N c : Nat) (h : Nat → ℝ) (hN : 2≤N)
    (hc : c<N) (hcodd : c%2=1) (hcenter : 0<h c)
    (hstep : ∀ j, j+1<N → h j*h (j+1)<0) :
    ∀ j, j<N → (j%2=0 → h j<0) ∧ (j%2=1 → 0<h j) := by
  have hzero : h 0<0 := by
    by_contra hh
    have hp := hstep 0 (by omega)
    have hn : h 0≠0 := by intro hz; simp [hz] at hp
    have hz : 0<h 0 := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hn)
    have hneg : (fun j => -h j) 0<0 := by simpa using neg_neg_of_pos hz
    have hsteps : ∀ j, j+1<N → (-h j)*(-h (j+1))<0 := by
      intro j hj
      simpa using hstep j hj
    have hh := (signs_from_negative N (fun j => -h j) hneg hsteps c hc).2 hcodd
    linarith
  exact signs_from_negative N h hzero hstep

/-- Saturation of all old Y0 segments forces the parity signs used by the
BBL interleaving. Here q=4r and the central old triangle points upward. -/
theorem saturated_alternation (r : Nat) (hr : 1≤r) (L : Nat → Line ℝ)
    (hp : NoParallel (4*r+1) L) (hs : NoConcurrent (4*r+1) L)
    (m a : Nat → ℝ) (h0 : L 0=graphLine 0 0)
    (hlines : ∀ j, j<4*r → L (j+1)=graphLine (m j) (a j))
    (hordered : ∀ j, j+1<4*r → a j<a (j+1))
    (htriangles : ∀ j, j<4*r-1 → TrianglePredicate (4*r+1) L ⟨0,j+1,j+2⟩)
    (hcentral : 0<(intersection (L (2*r)) (L (2*r+1))).2) :
    ∀ j, j<4*r-1 →
      (j%2=0 → (intersection (L (j+1)) (L (j+2))).2<0) ∧
      (j%2=1 → 0<(intersection (L (j+1)) (L (j+2))).2) := by
  let h := fun j => (intersection (L (j+1)) (L (j+2))).2
  apply signs_from_odd_center (4*r-1) (2*r-1) h (by omega) (by omega) (by omega)
  · simpa [h,show 2*r-1+1=2*r by omega,show 2*r-1+2=2*r+1 by omega] using hcentral
  · intro j hj
    exact consecutive_apices (4*r+1) L hp hs (j+1) (j+2) (j+3)
      (by omega) (by omega) (by omega) (by omega)
      (m j) (m (j+1)) (m (j+2)) (a j) (a (j+1)) (a (j+2))
      (hordered j (by omega)) (hordered (j+1) (by omega)) h0
      (hlines j (by omega)) (by simpa [Nat.add_assoc] using hlines (j+1) (by omega))
      (by simpa [Nat.add_assoc] using hlines (j+2) (by omega))
      (htriangles j (by omega)) (by simpa [Nat.add_assoc] using htriangles (j+1) (by omega))

#print axioms consecutive_apices
#print axioms saturated_alternation
end Kobon.BBLAlternation
