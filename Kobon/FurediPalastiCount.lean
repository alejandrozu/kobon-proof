import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite counting for the classical polygon construction. -/
namespace Kobon.FurediPalastiCount
open Finset

abbrev Triple (n : ℕ) := ZMod n × ZMod n × ZMod n
variable (n : ℕ) [NeZero n]

def sum (p : Triple n) : ZMod n := p.1+p.2.1+p.2.2
def distinct (p : Triple n) : Prop :=
  p.1≠p.2.1 ∧ p.1≠p.2.2 ∧ p.2.1≠p.2.2

def fiber (a : ZMod n) : Finset (Triple n) :=
  univ.image (fun p : ZMod n × ZMod n => (p.1,p.2,a-p.1-p.2))

theorem mem_fiber (a : ZMod n) (p : Triple n) :
    p ∈ fiber n a ↔ sum n p=a := by
  simp only [fiber,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,j⟩,rfl⟩
    simp [sum]
  · intro h
    refine ⟨(p.1,p.2.1),?_⟩
    dsimp [sum] at h
    have hk : a-p.1-p.2.1=p.2.2 := by rw [← h]; abel
    simp [hk]

theorem card_fiber (a : ZMod n) : (fiber n a).card=n*n := by
  have hi : Function.Injective (fun p : ZMod n × ZMod n => (p.1,p.2,a-p.1-p.2)) := by
    intro p q h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun r : Triple n => r.2.1) h
    exact Prod.ext h1 h2
  simp [fiber,Finset.card_image_of_injective _ hi,ZMod.card]

theorem disjoint_fiber (a b : ZMod n) (hab : a≠b) :
    Disjoint (fiber n a) (fiber n b) := by
  apply disjoint_left.mpr
  intro p hp hq
  exact hab ((mem_fiber n a p).mp hp |>.symm.trans ((mem_fiber n b p).mp hq))

def bad (a : ZMod n) : Finset (Triple n) :=
  (univ.image (fun i : ZMod n => (i,i,a-i-i))) ∪
  (univ.image (fun i : ZMod n => (i,a-i-i,i))) ∪
  (univ.image (fun i : ZMod n => (a-i-i,i,i)))

theorem card_bad_le (a : ZMod n) : (bad n a).card≤3*n := by
  have h1 := card_image_le (s:=univ) (f:=fun i : ZMod n => (i,i,a-i-i))
  have h2 := card_image_le (s:=univ) (f:=fun i : ZMod n => (i,a-i-i,i))
  have h3 := card_image_le (s:=univ) (f:=fun i : ZMod n => (a-i-i,i,i))
  have h4 := card_union_le
    (univ.image (fun i : ZMod n => (i,i,a-i-i)))
    (univ.image (fun i : ZMod n => (i,a-i-i,i)))
  have h5 := card_union_le
    ((univ.image (fun i : ZMod n => (i,i,a-i-i))) ∪
     (univ.image (fun i : ZMod n => (i,a-i-i,i))))
    (univ.image (fun i : ZMod n => (a-i-i,i,i)))
  simp only [card_univ,ZMod.card] at h1 h2 h3
  dsimp [bad]
  omega

theorem mem_bad (a : ZMod n) (p : Triple n)
    (hs : sum n p=a) (hd : ¬ distinct n p) : p ∈ bad n a := by
  rcases p with ⟨i,j,k⟩
  dsimp [sum,distinct] at hs hd
  simp only [bad,mem_union,mem_image,mem_univ,true_and]
  by_cases hij : i=j
  · subst j
    left; left
    refine ⟨i,?_⟩
    have h : a-i-i=k := by rw [← hs]; abel
    simp [h]
  · by_cases hik : i=k
    · subst k
      left; right
      refine ⟨i,?_⟩
      have h : a-i-i=j := by rw [← hs]; abel
      simp [h]
    · have hjk : j=k := by tauto
      subst k
      right
      refine ⟨j,?_⟩
      have h : a-j-j=i := by rw [← hs]; abel
      simp [h]

noncomputable def good (a b : ZMod n) : Finset (Triple n) := by
  classical
  exact (fiber n a ∪ fiber n b).filter (distinct n)

theorem mem_good (a b : ZMod n) (p : Triple n) :
    p ∈ good n a b ↔ (sum n p=a ∨ sum n p=b) ∧ distinct n p := by
  classical
  simp [good,mem_fiber]

theorem good_count (a b : ZMod n) (hab : a≠b) :
    2*(n*n) ≤ (good n a b).card+6*n := by
  classical
  let all := fiber n a ∪ fiber n b
  have hc : all.card=2*(n*n) := by
    dsimp [all]
    rw [card_union_of_disjoint (disjoint_fiber n a b hab),card_fiber,card_fiber]
    omega
  have hsplit := card_filter_add_card_filter_not (s:=all) (p:=distinct n)
  have hsub : all.filter (fun p => ¬distinct n p) ⊆ bad n a ∪ bad n b := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hp,hd⟩
    rcases mem_union.mp hp with hp | hp
    · exact mem_union_left _ (mem_bad n a p ((mem_fiber n a p).mp hp) hd)
    · exact mem_union_right _ (mem_bad n b p ((mem_fiber n b p).mp hp) hd)
  have hb := card_le_card hsub
  have hu := card_union_le (bad n a) (bad n b)
  have hba := card_bad_le n a
  have hbb := card_bad_le n b
  change (good n a b).card+_=_ at hsplit
  rw [hc] at hsplit
  omega

noncomputable def ordered (a b : ZMod n) : Finset (Triple n) := by
  classical
  exact univ.filter (fun p => (sum n p=a ∨ sum n p=b) ∧
    p.1.val<p.2.1.val ∧ p.2.1.val<p.2.2.val)

theorem mem_ordered (a b : ZMod n) (p : Triple n) :
    p∈ordered n a b ↔ (sum n p=a ∨ sum n p=b) ∧
      p.1.val<p.2.1.val ∧ p.2.1.val<p.2.2.val := by
  classical
  simp [ordered]

def orbit (p : Triple n) : Finset (Triple n) :=
  [p,(p.1,p.2.2,p.2.1),(p.2.1,p.1,p.2.2),
    (p.2.1,p.2.2,p.1),(p.2.2,p.1,p.2.1),(p.2.2,p.2.1,p.1)].toFinset

omit [NeZero n] in
theorem orbit_card (p : Triple n) : (orbit n p).card≤6 := by
  exact List.toFinset_card_le _

theorem good_subset_orbits (a b : ZMod n) :
    good n a b ⊆ (ordered n a b).biUnion (orbit n) := by
  classical
  rintro ⟨i,j,k⟩ hp
  rcases (mem_good n a b _).mp hp with ⟨hs,hd⟩
  have hij : i.val≠j.val := fun h => hd.1 (ZMod.val_injective n h)
  have hik : i.val≠k.val := fun h => hd.2.1 (ZMod.val_injective n h)
  have hjk : j.val≠k.val := fun h => hd.2.2 (ZMod.val_injective n h)
  have hs' : i+j+k=a ∨ i+j+k=b := hs
  by_cases h1 : i.val<j.val
  · by_cases h2 : j.val<k.val
    · apply mem_biUnion.mpr
      refine ⟨(i,j,k),(mem_ordered n a b _).mpr ⟨hs,h1,h2⟩,?_⟩
      simp [orbit]
    · by_cases h3 : i.val<k.val
      · apply mem_biUnion.mpr
        refine ⟨(i,k,j),(mem_ordered n a b _).mpr ⟨?_,h3,by dsimp; omega⟩,?_⟩
        · simpa [sum,add_comm,add_left_comm,add_assoc] using hs'
        · simp [orbit]
      · apply mem_biUnion.mpr
        refine ⟨(k,i,j),(mem_ordered n a b _).mpr ⟨?_,by dsimp; omega,h1⟩,?_⟩
        · simpa [sum,add_comm,add_left_comm,add_assoc] using hs'
        · simp [orbit]
  · by_cases h2 : i.val<k.val
    · apply mem_biUnion.mpr
      refine ⟨(j,i,k),(mem_ordered n a b _).mpr ⟨?_,by dsimp; omega,h2⟩,?_⟩
      · simpa [sum,add_comm,add_left_comm,add_assoc] using hs'
      · simp [orbit]
    · by_cases h3 : j.val<k.val
      · apply mem_biUnion.mpr
        refine ⟨(j,k,i),(mem_ordered n a b _).mpr ⟨?_,h3,by dsimp; omega⟩,?_⟩
        · simpa [sum,add_comm,add_left_comm,add_assoc] using hs'
        · simp [orbit]
      · apply mem_biUnion.mpr
        refine ⟨(k,j,i),(mem_ordered n a b _).mpr ⟨?_,by dsimp; omega,by dsimp; omega⟩,?_⟩
        · simpa [sum,add_comm,add_left_comm,add_assoc] using hs'
        · simp [orbit]

theorem good_le_six_ordered (a b : ZMod n) :
    (good n a b).card ≤ 6*(ordered n a b).card := by
  classical
  calc
    _ ≤ ((ordered n a b).biUnion (orbit n)).card := card_le_card (good_subset_orbits n a b)
    _ ≤ ∑ p ∈ ordered n a b, (orbit n p).card := card_biUnion_le
    _ ≤ ∑ _p ∈ ordered n a b, 6 := sum_le_sum (fun p _ => orbit_card n p)
    _ = _ := by simp [mul_comm]

theorem ordered_bound (hn : 3≤n) (a b : ZMod n) (hab : a≠b) :
    (n*(n-3)+2)/3 ≤ (ordered n a b).card := by
  have h1 := good_count n a b hab
  have h2 := good_le_six_ordered n a b
  have h3 : n-3+3=n := by omega
  have h4 : n*(n-3) ≤ 3*(ordered n a b).card := by nlinarith
  omega

end Kobon.FurediPalastiCount
