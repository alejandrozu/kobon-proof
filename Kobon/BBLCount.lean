import Kobon.BBLRowOrder
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Counting the mixed triangles in the integer BBL crossing-row model.
This module concerns an explicit finite integer model. Its geometric
realization is kept separate, so counting cannot assume its own conclusion.
-/
namespace Kobon.BBLCount
open Finset BBLRowOrder
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def neighbors (q : Nat) (K : Int) : Finset Nat :=
  (range q).filter (fun j => |K-oldKey j|<4)

def outside (q : Nat) (K : Int) : Prop := K<2 ∨ 4*(q:Int)-2<K

instance (q : Nat) (K : Int) : Decidable (outside q K) := inferInstanceAs (Decidable (_ ∨ _))

theorem neighbors_count (q : Nat) (hq : 2≤q) (K : Int)
    (hlo : -1≤K) (hhi : K≤4*(q:Int))
    (hne : ∀ j : Int, K≠oldKey j) :
    (neighbors q K).card + (if outside q K then 1 else 0)=2 := by
  by_cases hl : K<2
  · have heq : neighbors q K={0} := by
      ext j
      simp only [neighbors,mem_filter,mem_range,mem_singleton,abs_lt,oldKey]
      omega
    simp [heq,outside,hl]
  by_cases hh : 4*(q:Int)-2<K
  · have heq : neighbors q K={q-1} := by
      ext j
      simp only [neighbors,mem_filter,mem_range,mem_singleton,abs_lt,oldKey]
      omega
    simp [heq,outside,hh]
  have hklo : 3≤K := by have := hne 0; simp only [oldKey,mul_zero,zero_add] at this; omega
  have hkhi : K≤4*(q:Int)-3 := by
    have := hne ((q:Int)-1)
    simp only [oldKey] at this
    omega
  let d : Nat := ((K-2)/4).toNat
  have hd : (d:Int)=(K-2)/4 := by dsimp [d]; omega
  have hneq : K≠4*(d:Int)+2 := hne d
  have heq : neighbors q K={d,d+1} := by
    ext j
    simp only [neighbors,mem_filter,mem_range,mem_insert,mem_singleton,abs_lt,oldKey]
    omega
  have hdne : d≠d+1 := by omega
  simp [heq,hdne,outside,hl,hh]

def pairs (q : Nat) : Finset (Nat × Nat) :=
  (range (q+1)).biUnion (fun k => (range k).image (fun i => (i,k)))

theorem mem_pairs (q i k : Nat) : (i,k)∈pairs q ↔ i<k ∧ k≤q := by
  simp only [pairs,mem_biUnion,mem_range,mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,hbi,hak⟩
    subst b; subst a
    omega
  · rintro ⟨hik,hk⟩
    exact ⟨k,by omega,i,hik,rfl,rfl⟩

theorem pairs_count (q : Nat) : 2*(pairs q).card=q*(q+1) := by
  have hd : (range (q+1) : Set Nat).PairwiseDisjoint
      (fun k => (range k).image (fun i => (i,k))) := by
    intro k hk l hl hkl
    apply disjoint_left.mpr
    rintro p hp hq
    rcases mem_image.mp hp with ⟨i,hi,rfl⟩
    rcases mem_image.mp hq with ⟨j,hj,he⟩
    exact hkl (congrArg Prod.snd he).symm
  have hc (k : Nat) : ((range k).image (fun i => (i,k))).card=k := by
    rw [card_image_of_injective]
    · exact card_range k
    · intro i j h; exact congrArg Prod.fst h
  have hsum := sum_range_id_mul_two (q+1)
  simp only [Nat.add_sub_cancel] at hsum
  rw [pairs,card_biUnion hd]
  simp_rw [hc]
  nlinarith

def mixed (r : Nat) : Finset (Nat × Nat × Nat) :=
  (pairs (4*r)).biUnion (fun p =>
    (neighbors (4*r) (newKey (2*r) p.1 p.2)).image (fun j => (p.1,p.2,j)))

theorem mem_mixed (r i k j : Nat) : (i,k,j)∈mixed r ↔
    i<k ∧ k≤4*r ∧ j<4*r ∧ |newKey (2*r) i k-oldKey j|<4 := by
  simp only [mixed,mem_biUnion,mem_image,neighbors,mem_filter,mem_range]
  constructor
  · rintro ⟨⟨a,b⟩,hp,l,hl,he⟩
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun t : Nat × Nat × Nat => t.2.1) he
    have h3 := congrArg (fun t : Nat × Nat × Nat => t.2.2) he
    dsimp at h1 h2 h3
    subst a; subst b; subst l
    exact ⟨(mem_pairs _ _ _).mp hp |>.1,(mem_pairs _ _ _).mp hp |>.2,hl⟩
  · rintro ⟨hik,hk,hj,hclose⟩
    exact ⟨(i,k),(mem_pairs _ _ _).mpr ⟨hik,hk⟩,j,⟨hj,hclose⟩,rfl⟩

theorem mixed_card_sum (r : Nat) : (mixed r).card=
    ∑ p∈pairs (4*r), (neighbors (4*r) (newKey (2*r) p.1 p.2)).card := by
  have hd : (pairs (4*r) : Set (Nat × Nat)).PairwiseDisjoint (fun p =>
      (neighbors (4*r) (newKey (2*r) p.1 p.2)).image (fun j => (p.1,p.2,j))) := by
    intro p hp q hq hpq
    apply disjoint_left.mpr
    rintro t ht hu
    rcases mem_image.mp ht with ⟨j,hj,rfl⟩
    rcases mem_image.mp hu with ⟨k,hk,he⟩
    apply hpq
    apply Prod.ext
    · exact (congrArg Prod.fst he).symm
    · exact (congrArg (fun t : Nat × Nat × Nat => t.2.1) he).symm
  rw [mixed,card_biUnion hd]
  apply sum_congr rfl
  intro p hp
  apply card_image_of_injective
  intro j k he
  exact congrArg (fun t : Nat × Nat × Nat => t.2.2) he

def outsidePairs (r : Nat) : Finset (Nat × Nat) :=
  (pairs (4*r)).filter (fun p => outside (4*r) (newKey (2*r) p.1 p.2))

theorem outside_characterization (r i k : Nat) (hr : 1≤r)
    (hik : i<k) (hk : k≤4*r) :
    outside (4*r) (newKey (2*r) i k) ↔
      (i = 0 ∧ k = 4*r) ∨ (i = 4*r-1 ∧ k = 4*r) ∨
      (i+k = 2*r-1 ∧ k < 2*r) ∨ (i+k = 2*r ∧ k < 2*r) ∨
      (i+k = 6*r-1 ∧ 2*r ≤ i) ∨ (i+k = 6*r-2 ∧ 2*r ≤ i) := by
  unfold outside newKey
  push_cast
  split_ifs <;> omega

def outsideCover (r : Nat) : Finset (Nat × Nat) :=
  ((range r).image (fun i => (i,2*r-1-i))) ∪
  ((range (r-1)).image (fun i => (i+1,2*r-(i+1)))) ∪
  ((range r).image (fun i => (2*r+i,4*r-1-i))) ∪
  ((range (r-1)).image (fun i => (2*r+i,4*r-2-i))) ∪
  {(0,4*r),(4*r-1,4*r)}

theorem outside_subset (r : Nat) (hr : 1≤r) : outsidePairs r ⊆ outsideCover r := by
  rintro ⟨i,k⟩ hp
  rcases mem_filter.mp hp with ⟨hp,ho⟩
  rcases (mem_pairs _ _ _).mp hp with ⟨hik,hk⟩
  rcases (outside_characterization r i k hr hik hk).mp ho with
    h | h | h | h | h | h
  · rcases h with ⟨rfl,rfl⟩
    simp [outsideCover]
  · rcases h with ⟨rfl,rfl⟩
    simp [outsideCover]
  · simp only [outsideCover,mem_union,mem_image,mem_range,mem_insert,mem_singleton]
    left; left; left; left
    exact ⟨i,by omega,by congr 1 <;> omega⟩
  · simp only [outsideCover,mem_union,mem_image,mem_range,mem_insert,mem_singleton]
    left; left; left; right
    refine ⟨i-1,by omega,?_⟩
    congr 1 <;> omega
  · simp only [outsideCover,mem_union,mem_image,mem_range,mem_insert,mem_singleton]
    left; left; right
    refine ⟨i-2*r,by omega,?_⟩
    congr 1 <;> omega
  · simp only [outsideCover,mem_union,mem_image,mem_range,mem_insert,mem_singleton]
    left; right
    refine ⟨i-2*r,by omega,?_⟩
    congr 1 <;> omega

theorem outside_count_le (r : Nat) (hr : 1≤r) : (outsidePairs r).card≤4*r := by
  have h1 := card_image_le (s:=range r) (f:=fun i => (i,2*r-1-i))
  have h2 := card_image_le (s:=range (r-1)) (f:=fun i => (i+1,2*r-(i+1)))
  have h3 := card_image_le (s:=range r) (f:=fun i => (2*r+i,4*r-1-i))
  have h4 := card_image_le (s:=range (r-1)) (f:=fun i => (2*r+i,4*r-2-i))
  have h5 : ({(0,4*r),(4*r-1,4*r)} : Finset (Nat × Nat)).card≤2 := by
    exact card_insert_le _ _ |>.trans (by simp)
  have hu1 := card_union_le ((range r).image (fun i => (i,2*r-1-i)))
    ((range (r-1)).image (fun i => (i+1,2*r-(i+1))))
  have hu2 := card_union_le
    (((range r).image (fun i => (i,2*r-1-i))) ∪
     ((range (r-1)).image (fun i => (i+1,2*r-(i+1)))))
    ((range r).image (fun i => (2*r+i,4*r-1-i)))
  have hu3 := card_union_le
    ((((range r).image (fun i => (i,2*r-1-i))) ∪
      ((range (r-1)).image (fun i => (i+1,2*r-(i+1))))) ∪
      ((range r).image (fun i => (2*r+i,4*r-1-i))))
    ((range (r-1)).image (fun i => (2*r+i,4*r-2-i)))
  have hu4 := card_union_le
    (((((range r).image (fun i => (i,2*r-1-i))) ∪
       ((range (r-1)).image (fun i => (i+1,2*r-(i+1))))) ∪
       ((range r).image (fun i => (2*r+i,4*r-1-i)))) ∪
       ((range (r-1)).image (fun i => (2*r+i,4*r-2-i))))
    {(0,4*r),(4*r-1,4*r)}
  have hb := card_le_card (outside_subset r hr)
  simp only [card_range] at h1 h2 h3 h4
  dsimp [outsideCover] at hb
  omega

theorem mixed_count_identity (r : Nat) (hr : 1≤r) :
    (mixed r).card+(outsidePairs r).card=2*(pairs (4*r)).card := by
  rw [mixed_card_sum]
  have hsum : ∑ p∈pairs (4*r),
      ((neighbors (4*r) (newKey (2*r) p.1 p.2)).card+
        if outside (4*r) (newKey (2*r) p.1 p.2) then 1 else 0)=
      ∑ _p∈pairs (4*r), 2 := by
    apply sum_congr rfl
    rintro ⟨i,k⟩ hp
    rcases (mem_pairs _ _ _).mp hp with ⟨hik,hk⟩
    have hbounds := key_bounds (2*r) i k (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    apply neighbors_count _ (by omega) _
    · exact hbounds.1
    · convert hbounds.2 using 1 <;> push_cast <;> ring
    · exact newKey_ne_oldKey (2*r) i k
  rw [sum_add_distrib] at hsum
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at hsum
  have hc : (∑ p∈pairs (4*r), if outside (4*r) (newKey (2*r) p.1 p.2) then 1 else 0)=
      (outsidePairs r).card := by simp [outsidePairs]
  rw [hc] at hsum
  simpa only [mul_comm] using hsum

/-- At least q² mixed triangles in the explicit model, for q=4*r. -/
theorem mixed_count (r : Nat) (hr : 1≤r) : (4*r)^2≤(mixed r).card := by
  have hc := mixed_count_identity r hr
  have hp := pairs_count (4*r)
  have ho := outside_count_le r hr
  nlinarith

#print axioms mixed_count

end Kobon.BBLCount
