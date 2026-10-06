import Kobon.Geometry
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Exact infinitesimal one-line translation certificates at every order.
Normal coefficients stay fixed, so all vertex-side tests are affine in ε.
Their eventual signs are determined by the constant coefficient, followed by
the linear coefficient. One positive threshold works simultaneously for all
supporting triples and all line-side predicates in a finite arrangement.
-/
namespace Kobon.OpenMathTranslationGerms

def Small (P : ℝ → Prop) : Prop :=
  ∃ η : ℝ, 0<η ∧ ∀ ε : ℝ, 0<ε → ε<η → P ε

theorem Small.const {p : Prop} (h : p) : Small (fun _=>p) :=
  ⟨1,by norm_num,fun _ _ _=>h⟩

theorem Small.mono {P Q : ℝ → Prop} (h : Small P) (hm : ∀ ε, P ε → Q ε) : Small Q := by
  rcases h with ⟨η,hη,h⟩
  exact ⟨η,hη,fun ε he hs=>hm ε (h ε he hs)⟩

theorem Small.and {P Q : ℝ → Prop} (hp : Small P) (hq : Small Q) :
    Small (fun ε=>P ε ∧ Q ε) := by
  rcases hp with ⟨a,ha,hp⟩
  rcases hq with ⟨b,hb,hq⟩
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro ε he hs
  exact ⟨hp ε he (lt_of_lt_of_le hs (min_le_left _ _)),
    hq ε he (lt_of_lt_of_le hs (min_le_right _ _))⟩

theorem Small.and_iff {P Q : ℝ → Prop} {p q : Prop}
    (hp : Small (fun ε=>P ε↔p)) (hq : Small (fun ε=>Q ε↔q)) :
    Small (fun ε=>(P ε∧Q ε)↔(p∧q)) :=
  (hp.and hq).mono (fun _ h=>and_congr h.1 h.2)

theorem Small.or_iff {P Q : ℝ → Prop} {p q : Prop}
    (hp : Small (fun ε=>P ε↔p)) (hq : Small (fun ε=>Q ε↔q)) :
    Small (fun ε=>(P ε∨Q ε)↔(p∨q)) :=
  (hp.and hq).mono (fun _ h=>or_congr h.1 h.2)

theorem Small.all_fin (n : ℕ) (P : Fin n → ℝ → Prop)
    (h : ∀ i, Small (P i)) : Small (fun ε=>∀ i, P i ε) := by
  induction n with
  | zero => exact ⟨1,by norm_num,fun _ _ _ i=>Fin.elim0 i⟩
  | succ n ih =>
    have ht := ih (fun i ε=>P i.succ ε) (fun i=>h i.succ)
    exact ((h 0).and ht).mono (fun ε hh=>Fin.cases hh.1 (fun i=>hh.2 i))

theorem Small.all_fin_iff (n : ℕ) (P : Fin n → ℝ → Prop) (p : Fin n → Prop)
    (h : ∀ i, Small (fun ε=>P i ε↔p i)) :
    Small (fun ε=>(∀ i,P i ε)↔∀ i,p i) :=
  (Small.all_fin n (fun i ε=>P i ε↔p i) h).mono
    (fun _ hh=>forall_congr' hh)

def Nonnegative (a b : ℝ) : Prop := 0<a ∨ (a=0 ∧ 0≤b)
def Nonpositive (a b : ℝ) : Prop := Nonnegative (-a) (-b)
def Nonzero (a b : ℝ) : Prop := a≠0 ∨ b≠0

theorem positive_constant_stable (a b : ℝ) (ha : 0<a) :
    Small (fun ε=>0<a+b*ε) := by
  have hd : 0<abs b+1 := by positivity
  refine ⟨a/(abs b+1),div_pos ha hd,?_⟩
  intro ε he hs
  have hbound : ε*(abs b+1)<a := (lt_div_iff₀ hd).mp hs
  have hneg : -(abs b)*ε≤b*ε := mul_le_mul_of_nonneg_right (neg_abs_le b) (le_of_lt he)
  nlinarith [abs_nonneg b]

theorem negative_constant_stable (a b : ℝ) (ha : a<0) :
    Small (fun ε=>a+b*ε<0) := by
  have hp := positive_constant_stable (-a) (-b) (by linarith)
  exact hp.mono (fun ε h=>by nlinarith)

theorem nonnegative_stable (a b : ℝ) :
    Small (fun ε=>(0≤a+b*ε)↔Nonnegative a b) := by
  rcases lt_trichotomy a 0 with ha|ha|ha
  · apply (negative_constant_stable a b ha).mono
    intro ε h
    constructor
    · intro hh; linarith
    · rintro (hh|⟨hh,_⟩) <;> linarith
  · subst a
    by_cases hb : 0≤b
    · refine ⟨1,by norm_num,?_⟩
      intro ε he _
      have hm : 0≤b*ε := mul_nonneg hb (le_of_lt he)
      simp [Nonnegative,hb,hm]
    · refine ⟨1,by norm_num,?_⟩
      intro ε he _
      have hm : b*ε<0 := mul_neg_of_neg_of_pos (lt_of_not_ge hb) he
      constructor
      · intro hh; simp only [zero_add] at hh; linarith
      · simp [Nonnegative,hb]
  · apply (positive_constant_stable a b ha).mono
    intro ε h
    exact ⟨fun _=>Or.inl ha,fun _=>le_of_lt h⟩

theorem nonpositive_stable (a b : ℝ) :
    Small (fun ε=>(a+b*ε≤0)↔Nonpositive a b) := by
  have hh := nonnegative_stable (-a) (-b)
  apply hh.mono
  intro ε h
  have heq : -a+(-b)*ε=-(a+b*ε) := by ring
  simpa only [heq,neg_nonneg,Nonpositive] using h

theorem nonzero_stable (a b : ℝ) :
    Small (fun ε=>(a+b*ε≠0)↔Nonzero a b) := by
  by_cases ha : a=0
  · subst a
    refine ⟨1,by norm_num,?_⟩
    intro ε he _
    simp [Nonzero,mul_ne_zero,ne_of_gt he]
  · rcases lt_or_gt_of_ne ha with hn|hp
    · apply (negative_constant_stable a b hn).mono
      intro ε h
      exact ⟨fun _=>Or.inl ha,fun _=>ne_of_lt h⟩
    · apply (positive_constant_stable a b hp).mono
      intro ε h
      exact ⟨fun _=>Or.inl ha,fun _=>ne_of_gt h⟩

def translate (L : ℕ → Line ℝ) (p : ℕ) (ε : ℝ) (i : ℕ) : Line ℝ :=
  ⟨(L i).a,(L i).b,(L i).c+(if i=p then ε else 0)⟩

theorem translate_zero (L : ℕ → Line ℝ) (p : ℕ) (i : ℕ) : translate L p 0 i=L i := by
  simp [translate]

theorem det_translate (L : ℕ → Line ℝ) (p : ℕ) (ε : ℝ) (i j : ℕ) :
    det (translate L p ε i) (translate L p ε j)=det (L i) (L j) := rfl

def evalSlope (L : ℕ → Line ℝ) (p r i j : ℕ) : ℝ :=
  evalVertex (translate L p 1 r) (translate L p 1 i) (translate L p 1 j)-
    evalVertex (L r) (L i) (L j)

def sideSlope (L : ℕ → Line ℝ) (p r i j : ℕ) : ℝ :=
  orientedEval (translate L p 1 r) (translate L p 1 i) (translate L p 1 j)-
    orientedEval (L r) (L i) (L j)

theorem eval_translate_affine (L : ℕ → Line ℝ) (p r i j : ℕ) (ε : ℝ) :
    evalVertex (translate L p ε r) (translate L p ε i) (translate L p ε j)=
      evalVertex (L r) (L i) (L j)+evalSlope L p r i j*ε := by
  unfold evalSlope evalVertex vertex det translate
  split_ifs <;> ring

theorem side_translate_affine (L : ℕ → Line ℝ) (p r i j : ℕ) (ε : ℝ) :
    orientedEval (translate L p ε r) (translate L p ε i) (translate L p ε j)=
      orientedEval (L r) (L i) (L j)+sideSlope L p r i j*ε := by
  unfold sideSlope orientedEval evalVertex vertex det translate
  split_ifs <;> ring

theorem translate_no_parallel (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) (ε : ℝ)
    (hp : NoParallel n L) : NoParallel n (translate L p ε) := by
  intro i j hij
  simpa only [det_translate] using hp i j hij

def TriangleGerm (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) (t : Triple) : Prop :=
  t.i<t.j ∧ t.j<t.k ∧ t.k<n ∧
  Nonzero (evalVertex (L t.k) (L t.i) (L t.j)) (evalSlope L p t.k t.i t.j) ∧
  ∀ r : Fin n,
    (Nonnegative (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j) ∧
     Nonnegative (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k) ∧
     Nonnegative (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k)) ∨
    (Nonpositive (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j) ∧
     Nonpositive (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k) ∧
     Nonpositive (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k))

theorem triangle_stable (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) (t : Triple) :
    Small (fun ε=>TrianglePredicate n (translate L p ε) t↔TriangleGerm n L p t) := by
  have hn : Small (fun ε=>evalVertex (translate L p ε t.k)
      (translate L p ε t.i) (translate L p ε t.j)≠0 ↔
      Nonzero (evalVertex (L t.k) (L t.i) (L t.j)) (evalSlope L p t.k t.i t.j)) := by
    simpa only [eval_translate_affine] using
      nonzero_stable (evalVertex (L t.k) (L t.i) (L t.j)) (evalSlope L p t.k t.i t.j)
  have hs (r : Fin n) : Small (fun ε=>
      ((0≤orientedEval (translate L p ε r) (translate L p ε t.i) (translate L p ε t.j) ∧
        0≤orientedEval (translate L p ε r) (translate L p ε t.i) (translate L p ε t.k) ∧
        0≤orientedEval (translate L p ε r) (translate L p ε t.j) (translate L p ε t.k)) ∨
       (orientedEval (translate L p ε r) (translate L p ε t.i) (translate L p ε t.j)≤0 ∧
        orientedEval (translate L p ε r) (translate L p ε t.i) (translate L p ε t.k)≤0 ∧
        orientedEval (translate L p ε r) (translate L p ε t.j) (translate L p ε t.k)≤0)) ↔
      ((Nonnegative (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j) ∧
        Nonnegative (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k) ∧
        Nonnegative (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k)) ∨
       (Nonpositive (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j) ∧
        Nonpositive (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k) ∧
        Nonpositive (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k)))) := by
    have hpos := Small.and_iff
      (nonnegative_stable (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j))
      (Small.and_iff
        (nonnegative_stable (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k))
        (nonnegative_stable (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k)))
    have hneg := Small.and_iff
      (nonpositive_stable (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j))
      (Small.and_iff
        (nonpositive_stable (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k))
        (nonpositive_stable (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k)))
    simpa only [side_translate_affine] using Small.or_iff hpos hneg
  exact Small.and_iff (Small.const Iff.rfl)
    (Small.and_iff (Small.const Iff.rfl)
      (Small.and_iff (Small.const Iff.rfl)
        (Small.and_iff hn (Small.all_fin_iff n _ _ hs))))

/-- One positive ε threshold classifies every possible supporting triple. -/
theorem simultaneous_triangle_stability (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) :
    ∃ η : ℝ, 0<η ∧ ∀ ε : ℝ, 0<ε → ε<η → ∀ i j k : Fin n,
      TrianglePredicate n (translate L p ε) ⟨i,j,k⟩↔TriangleGerm n L p ⟨i,j,k⟩ := by
  apply Small.all_fin n
  intro i
  apply Small.all_fin n
  intro j
  apply Small.all_fin n
  intro k
  exact triangle_stable n L p ⟨i,j,k⟩

#print axioms eval_translate_affine
#print axioms triangle_stable
#print axioms simultaneous_triangle_stability
end Kobon.OpenMathTranslationGerms
