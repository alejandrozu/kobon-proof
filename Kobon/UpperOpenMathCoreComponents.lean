import Kobon.UpperOpenMathCoreDoubleCount
import Kobon.UpperOpenMathCapHeavyTriples
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-! Actual shared-core components and their exact local defect cost. -/
namespace Kobon.UpperOpenMathCoreComponents
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples Finset
open scoped BigOperators

def SharedCoreClosed {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) : Prop :=
  ∀ e∈twoCoreEdges n L G, ∀ p∈e, p∈P → e⊆P

noncomputable def componentEdges {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) : Finset Edge := by
  classical
  exact (twoCoreEdges n L G).filter (fun e => e⊆P)

noncomputable def componentCost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) : ℤ :=
  (∑ p∈P, (supports n L p).card*((supports n L p).card-2 : ℤ))-
  (∑ p∈P, (ordinaryDegree n L G p : ℤ))-(componentEdges n L G P).card

theorem closed_degree_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point)
    (closed : SharedCoreClosed n L G P) :
    (∑ p∈P, coreDegree n L G p)=2*(componentEdges n L G P).card := by
  classical
  change (∑ p∈P, ((twoCoreEdges n L G).filter (fun e => p∈e)).card)=_
  rw [UpperOpenMathCoreDoubleCount.endpoint_double_count]
  have hEach (e : Edge) (he : e∈twoCoreEdges n L G) :
      (e∩P).card=(if e⊆P then 2 else 0) := by
    by_cases hsub : e⊆P
    · rw [if_pos hsub,inter_eq_left.mpr hsub]
      exact used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1
    · rw [if_neg hsub]
      have hempty : e∩P=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hpe,hpP⟩ := mem_inter.mp hp
        exact hsub (closed e he p hpe hpP)
      simp only [hempty,card_empty]
  calc
    _=∑ e∈twoCoreEdges n L G, (if e⊆P then 2 else 0) := sum_congr rfl hEach
    _=∑ _e∈componentEdges n L G P, 2 := by rw [componentEdges,sum_filter]
    _=2*(componentEdges n L G P).card := by simp [Nat.mul_comm]

def CoreVertex (n : ℕ) (L : ℕ → Line ℝ) := {p : Point // p∈core n L}

noncomputable instance coreVertexFintype (n : ℕ) (L : ℕ → Line ℝ) : Fintype (CoreVertex n L) := by
  classical
  unfold CoreVertex
  infer_instance

noncomputable def coreGraph {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : SimpleGraph (CoreVertex n L) where
  Adj p q := p≠q ∧ ({p.val,q.val} : Edge)∈twoCoreEdges n L G
  symm := ⟨by
    intro p q h
    exact ⟨h.1.symm,by simpa only [pair_comm] using h.2⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

noncomputable def componentVertices {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (s : (coreGraph n L G).ConnectedComponent) : Finset Point := by
  classical
  exact (univ.filter (fun p : CoreVertex n L =>
    (coreGraph n L G).connectedComponentMk p=s)).image Subtype.val

noncomputable def coreComponentCount {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : ℕ :=
  Nat.card (coreGraph n L G).ConnectedComponent

noncomputable def components {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    Finset (coreGraph n L G).ConnectedComponent := by
  classical
  exact univ

theorem components_mem {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (s : (coreGraph n L G).ConnectedComponent) : s∈components n L G := by
  classical
  simp [components]

theorem components_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    (components n L G).card=coreComponentCount n L G := by
  classical
  simp [components,coreComponentCount,Nat.card_eq_fintype_card]

theorem mem_component {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (s : (coreGraph n L G).ConnectedComponent) (p : CoreVertex n L) :
    p.val∈componentVertices n L G s ↔ (coreGraph n L G).connectedComponentMk p=s := by
  classical
  constructor
  · intro hp
    obtain ⟨q,hq,he⟩ := mem_image.mp hp
    have hqp : q=p := Subtype.ext he
    simpa only [hqp] using (mem_filter.mp hq).2
  · intro hp
    exact mem_image.mpr ⟨p,mem_filter.mpr ⟨mem_univ p,hp⟩,rfl⟩

theorem component_subset {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (s : (coreGraph n L G).ConnectedComponent) : componentVertices n L G s⊆core n L := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
  exact q.property

theorem component_support_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (s : (coreGraph n L G).ConnectedComponent) :
    Nat.card s.supp=(componentVertices n L G s).card := by
  classical
  let equivalence : s.supp ≃ {p : Point // p∈componentVertices n L G s} := {
    toFun := fun p => ⟨p.val.val,(mem_component n L G s p.val).mpr
      ((SimpleGraph.ConnectedComponent.mem_supp_iff s p.val).mp p.property)⟩
    invFun := fun p => ⟨⟨p.val,component_subset n L G s p.property⟩,
      (SimpleGraph.ConnectedComponent.mem_supp_iff s _).mpr
        ((mem_component n L G s _).mp p.property)⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl
  }
  rw [Nat.card_congr equivalence]
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe]

theorem component_nonempty {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (s : (coreGraph n L G).ConnectedComponent) : (componentVertices n L G s).Nonempty := by
  exact SimpleGraph.ConnectedComponent.ind
    (fun p => ⟨p.val,(mem_component n L G _ p).mpr rfl⟩) s

theorem component_closed {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (s : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).ConnectedComponent) :
    SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a))
      (componentVertices n L (fun a => ofPredicate n L (tri a) hL (ht a)) s) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  intro e he p hpe hpP q hqe
  have hsub := (mem_powersetCard.mp (UpperCoreCombinatorics.core_edge_subset n L hL tri ht he)).1
  let pp : CoreVertex n L := ⟨p,hsub hpe⟩
  let qq : CoreVertex n L := ⟨q,hsub hqe⟩
  have hpComp := (mem_component n L G s pp).mp hpP
  by_cases hqp : q=p
  · simpa only [hqp] using hpP
  have hpq : pp≠qq := by intro h; exact hqp (congrArg Subtype.val h).symm
  have hpair : e={p,q} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro x hx
      rcases mem_insert.mp hx with hx|hx
      · simpa only [hx] using hpe
      · simpa only [mem_singleton.mp hx] using hqe
    · rw [card_pair (Ne.symm hqp),used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
  have adj : (coreGraph n L G).Adj pp qq := ⟨hpq,by simpa only [hpair] using he⟩
  apply (mem_component n L G s qq).mpr
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj adj).symm.trans hpComp

theorem component_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (f : Point → ℤ) :
    (∑ s∈components n L G, ∑ p∈componentVertices n L G s, f p)=∑ p∈core n L, f p := by
  classical
  have disj : (↑(components n L G) : Set (coreGraph n L G).ConnectedComponent).PairwiseDisjoint
      (componentVertices n L G) := by
    intro s hs t ht hne
    apply disjoint_left.mpr
    intro p hpS hpT
    let pp : CoreVertex n L := ⟨p,component_subset n L G s hpS⟩
    have hS := (mem_component n L G s pp).mp hpS
    have hT := (mem_component n L G t pp).mp hpT
    exact hne (hS.symm.trans hT)
  have cover : (components n L G).biUnion (componentVertices n L G)=core n L := by
    ext p
    constructor
    · intro hp
      obtain ⟨s,hs,hps⟩ := mem_biUnion.mp hp
      exact component_subset n L G s hps
    · intro hp
      let pp : CoreVertex n L := ⟨p,hp⟩
      let s := (coreGraph n L G).connectedComponentMk pp
      exact mem_biUnion.mpr ⟨s,components_mem n L G s,(mem_component n L G s pp).mpr rfl⟩
  rw [← cover,sum_biUnion disj]

theorem component_edges_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ s∈components n L G, (componentEdges n L G (componentVertices n L G s)).card)=
      (twoCoreEdges n L G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  change (∑ s∈components n L G,
    ((twoCoreEdges n L G).filter (fun e => e⊆componentVertices n L G s)).card)=_
  simp only [card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
  have ec := used_edge_card G hused
  obtain ⟨p,hpe⟩ := card_pos.mp (by omega : 0<e.card)
  have hsubCore := (mem_powersetCard.mp (UpperCoreCombinatorics.core_edge_subset n L hL tri ht he)).1
  let pp : CoreVertex n L := ⟨p,hsubCore hpe⟩
  let s := (coreGraph n L G).connectedComponentMk pp
  have hpS : p∈componentVertices n L G s := (mem_component n L G s pp).mpr rfl
  have esub : e⊆componentVertices n L G s := component_closed n L hL tri ht s e he p hpe hpS
  calc
    _=(if e⊆componentVertices n L G s then (1 : ℕ) else 0) := by
      apply sum_eq_single s
      · intro t ht hne
        apply if_neg
        intro hsub
        have eq : s=t := (mem_component n L G t pp).mp (hsub hpe)
        exact hne eq.symm
      · intro hnot
        exact False.elim (hnot (components_mem n L G s))
    _=1 := if_pos esub

theorem component_vertices_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    (∑ s∈components n L G, (componentVertices n L G s).card)=(core n L).card := by
  have h := component_sum n L G (fun _ => (1 : ℤ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at h
  exact_mod_cast h

theorem certificate_component_cost_identity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)*(n-2)-3*Fintype.card α=
      (UpperEdgeInventory.edges n L\usedEdges G).card+
      ∑ s∈components n L G, componentCost n L G (componentVertices n L G s) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hedges := component_edges_sum n L hL tri ht
  have hedgesZ : (∑ s∈components n L G,
      ((componentEdges n L G (componentVertices n L G s)).card : ℤ))=(twoCoreEdges n L G).card := by
    exact_mod_cast hedges
  have hone := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  have honeZ : (∑ p∈core n L, (ordinaryDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by
    exact_mod_cast hone
  have hcost : (∑ s∈components n L G, componentCost n L G (componentVertices n L G s))=
      (∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      (oneCoreEdges n L G).card-(twoCoreEdges n L G).card := by
    simp only [componentCost,sum_sub_distrib]
    rw [component_sum,component_sum,honeZ,hedgesZ]
  have hid := defect_identity n L hL hn tri hi ht
  dsimp only at hid
  dsimp only
  rw [hcost]
  linarith

#print axioms closed_degree_sum
#print axioms component_closed
#print axioms certificate_component_cost_identity
#print axioms component_support_card
end Kobon.UpperOpenMathCoreComponents
