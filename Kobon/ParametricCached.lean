import Kobon.Parametric

/-! Extensionally identical finite checks with materialized form coefficients.
This avoids recomputing rational coefficient expressions in every interval
comparison. Soundness is proved by exact equality with the original checks. -/
namespace Kobon.ParametricCached
open Parametric
set_option autoImplicit false

def cache {d : Nat} (f : Form d) : Form d :=
  let xs := Array.ofFn f
  fun i => xs[i.val]'(by simpa only [xs,Array.size_ofFn] using i.isLt)

theorem cache_eq {d : Nat} (f : Form d) : cache f=f := by
  funext i
  simp [cache]

def SimpleCheck {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : Prop :=
  ∀ i j k : Fin n, i<j → j<k →
    NonzeroCert lo hi (cache (evalForm (L k) (L i) (L j))) e

instance {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : Decidable (SimpleCheck n lo hi e L) := by
  unfold SimpleCheck
  infer_instance

theorem simple_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) (h : SimpleCheck n lo hi e L) :
    Parametric.SimpleCheck n lo hi e L := by
  simpa only [SimpleCheck,cache_eq,Parametric.SimpleCheck] using h

def TriangleCheck {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (t : Triple) : Prop :=
  t.i<t.j ∧ t.j<t.k ∧ t.k<n ∧ ∀ r : Fin n,
    let f := cache (orientedForm (L r) (L t.i) (L t.j))
    let g := cache (orientedForm (L r) (L t.i) (L t.k))
    let h := cache (orientedForm (L r) (L t.j) (L t.k))
    (0≤lower lo hi f ∧ 0≤lower lo hi g ∧ 0≤lower lo hi h) ∨
    (upper lo hi f≤0 ∧ upper lo hi g≤0 ∧ upper lo hi h≤0)

instance {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (t : Triple) : Decidable (TriangleCheck n lo hi L t) := by
  unfold TriangleCheck
  infer_instance

theorem triangle_eq {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (t : Triple) :
    TriangleCheck n lo hi L t=Parametric.TriangleCheck n lo hi L t := by
  simp only [TriangleCheck,cache_eq,Parametric.TriangleCheck]

#print axioms simple_sound
#print axioms triangle_eq
end Kobon.ParametricCached
