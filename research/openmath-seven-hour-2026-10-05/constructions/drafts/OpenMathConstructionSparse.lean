import Kobon.OpenMathConstructionBoolean

/-! Sparse versions of exactly the same finite parametric checks.
A single-coordinate intercept form makes each three-line evaluation supported
on at most three coordinates. Summing only over that support is proved equal
to the full interval sum, so this is an executable optimization, not a
weaker geometric or interval certificate.
-/
namespace Kobon.OpenMathConstructionSparse
open Parametric HybridBoundary
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure SparseLine (d : Nat) where
  a : ℚ
  b : ℚ
  pos : Fin d
  c : ℚ

instance {d : Nat} [NeZero d] : Inhabited (SparseLine d) := ⟨⟨0,0,0,0⟩⟩

def toParam {d : Nat} (l : SparseLine d) : ParamLine d :=
  ⟨l.a,l.b,fun i => if i=l.pos then l.c else 0⟩

def support {d : Nat} (r l m : SparseLine d) : Finset (Fin d) :=
  {r.pos,l.pos,m.pos}

theorem eval_zero_off {d : Nat} (r l m : SparseLine d) (i : Fin d)
    (hi : i∉support r l m) : evalForm (toParam r) (toParam l) (toParam m) i=0 := by
  have hh : i≠r.pos ∧ i≠l.pos ∧ i≠m.pos := by simpa [support] using hi
  simp [evalForm,scale,toParam,hh.1,hh.2.1,hh.2.2]

theorem oriented_zero_off {d : Nat} (r l m : SparseLine d) (i : Fin d)
    (hi : i∉support r l m) : orientedForm (toParam r) (toParam l) (toParam m) i=0 := by
  simp only [orientedForm,scale,eval_zero_off r l m i hi,mul_zero]

def lowerOn {d : Nat} (s : Finset (Fin d)) (lo hi f : Form d) : ℚ :=
  ∑ i∈s, let c := f i; if 0≤c then c*lo i else c*hi i

def upperOn {d : Nat} (s : Finset (Fin d)) (lo hi f : Form d) : ℚ :=
  ∑ i∈s, let c := f i; if 0≤c then c*hi i else c*lo i

theorem lowerOn_eq {d : Nat} (s : Finset (Fin d)) (lo hi f : Form d)
    (hz : ∀ i, i∉s → f i=0) : lowerOn s lo hi f=lower lo hi f := by
  unfold lowerOn lower
  apply Finset.sum_subset (Finset.subset_univ s)
  intro i _ his
  simp [hz i his]

theorem upperOn_eq {d : Nat} (s : Finset (Fin d)) (lo hi f : Form d)
    (hz : ∀ i, i∉s → f i=0) : upperOn s lo hi f=upper lo hi f := by
  unfold upperOn upper
  apply Finset.sum_subset (Finset.subset_univ s)
  intro i _ his
  simp [hz i his]

def nonzeroBool {d : Nat} (lo hi f : Form d) (e : Fin d) (s : Finset (Fin d)) : Bool :=
  decide (0<lowerOn s lo hi f) || decide (upperOn s lo hi f<0) ||
    (OpenMathConstructionBoolean.allFin d (fun i => if i=e then true else decide (f i=0)) && decide (f e≠0))

theorem nonzero_sound {d : Nat} (lo hi f : Form d) (e : Fin d) (s : Finset (Fin d))
    (hz : ∀ i, i∉s → f i=0) (h : nonzeroBool lo hi f e s=true) :
    NonzeroCert lo hi f e := by
  simp only [nonzeroBool,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with (hp | hn) | ⟨hs,he⟩
  · exact Or.inl (by simpa only [lowerOn_eq s lo hi f hz] using hp)
  · exact Or.inr (Or.inl (by simpa only [upperOn_eq s lo hi f hz] using hn))
  · refine Or.inr (Or.inr ⟨?_,he⟩)
    intro i hie
    have hh := (OpenMathConstructionBoolean.allFin_true d _).mp hs i
    simpa only [if_neg hie,decide_eq_true_eq] using hh

def simpleBool {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→SparseLine d) : Bool :=
  OpenMathConstructionBoolean.allFin n fun i =>
    OpenMathConstructionBoolean.allFin n fun j =>
      OpenMathConstructionBoolean.allFin n fun k =>
        if i<j ∧ j<k then
          let r := L k; let l := L i; let m := L j
          nonzeroBool lo hi (evalForm (toParam r) (toParam l) (toParam m)) e (support r l m)
        else true

theorem simple_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→SparseLine d) (h : simpleBool n lo hi e L=true) :
    SimpleCheck n lo hi e (fun i => toParam (L i)) := by
  intro i j k hij hjk
  have h1 := (OpenMathConstructionBoolean.allFin_true n _).mp h i
  have h2 := (OpenMathConstructionBoolean.allFin_true n _).mp h1 j
  have h3 := (OpenMathConstructionBoolean.allFin_true n _).mp h2 k
  have hik : i<j ∧ j<k := ⟨hij,hjk⟩
  have hh : nonzeroBool lo hi (evalForm (toParam (L k)) (toParam (L i)) (toParam (L j))) e
      (support (L k) (L i) (L j))=true := by simpa only [if_pos hik] using h3
  exact nonzero_sound lo hi _ e _ (eval_zero_off (L k) (L i) (L j)) hh

def triangleBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→SparseLine d) (t : Triple) : Bool :=
  decide (t.i<t.j) && decide (t.j<t.k) && decide (t.k<n) &&
    OpenMathConstructionBoolean.allFin n fun r =>
      let f := orientedForm (toParam (L r)) (toParam (L t.i)) (toParam (L t.j))
      let g := orientedForm (toParam (L r)) (toParam (L t.i)) (toParam (L t.k))
      let h := orientedForm (toParam (L r)) (toParam (L t.j)) (toParam (L t.k))
      let sf := support (L r) (L t.i) (L t.j)
      let sg := support (L r) (L t.i) (L t.k)
      let sh := support (L r) (L t.j) (L t.k)
      (decide (0≤lowerOn sf lo hi f) && decide (0≤lowerOn sg lo hi g) && decide (0≤lowerOn sh lo hi h)) ||
      (decide (upperOn sf lo hi f≤0) && decide (upperOn sg lo hi g≤0) && decide (upperOn sh lo hi h≤0))

theorem triangle_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→SparseLine d) (t : Triple) (h : triangleBool n lo hi L t=true) :
    TriangleCheck n lo hi (fun i => toParam (L i)) t := by
  simp only [triangleBool,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hi,hj⟩,hk⟩,hr⟩
  refine ⟨hi,hj,hk,?_⟩
  intro r
  have hh := (OpenMathConstructionBoolean.allFin_true n _).mp hr r
  simpa only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc,
    lowerOn_eq _ _ _ _ (oriented_zero_off (L r) (L t.i) (L t.j)),
    lowerOn_eq _ _ _ _ (oriented_zero_off (L r) (L t.i) (L t.k)),
    lowerOn_eq _ _ _ _ (oriented_zero_off (L r) (L t.j) (L t.k)),
    upperOn_eq _ _ _ _ (oriented_zero_off (L r) (L t.i) (L t.j)),
    upperOn_eq _ _ _ _ (oriented_zero_off (L r) (L t.i) (L t.k)),
    upperOn_eq _ _ _ _ (oriented_zero_off (L r) (L t.j) (L t.k))] using hh

def trianglesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→SparseLine d) (ts : List Triple) : Bool := ts.all (triangleBool n lo hi L)

theorem triangles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→SparseLine d) (ts : List Triple) (h : trianglesBool n lo hi L ts=true) :
    ts.all (fun t => decide (TriangleCheck n lo hi (fun i => toParam (L i)) t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact triangle_sound n lo hi L t ((List.all_eq_true.mp h) t ht)

#print axioms simple_sound
#print axioms triangle_sound
end Kobon.OpenMathConstructionSparse