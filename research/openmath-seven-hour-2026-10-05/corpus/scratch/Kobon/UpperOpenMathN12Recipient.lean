import Kobon.UpperOpenMathN13ActualChart
import Kobon.UpperOpenMathN13OrdinaryActual
import Kobon.UpperOpenMathUnmarkedCrossResources

/-! A one-cap degree-two recipient cannot meet two antipodal full sources. -/
namespace Kobon.UpperOpenMathN12Recipient
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathSectorRecords UpperOpenMathActualFans UpperOpenMathCapHeavyTriples
  UpperOpenMathAntipodalAdjacency UpperOpenMathAntipodalFullNeighborPair
  UpperOpenMathAntipodalTwoCapChart UpperOpenMathN13ActualChart
  UpperOpenMathUnmarkedCrossResources Finset
set_option maxHeartbeats 1000000

theorem lift_n12_counts {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (f : Sectors n r L) (hr : r=3)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (pos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (occ : ∀ z∈f.triangular, Nonempty (Occurrence G f.center f.point z))
    (ac : f.ordinaryShared.card=1) (dc : f.coreShared.card=2) :
    ∃ g : Sectors n 3 L, g.center=f.center ∧ AnyChartData G g ∧
      g.ordinaryShared.card=1 ∧ g.coreShared.card=2 := by
  subst r
  exact ⟨f,rfl,⟨inj,nc,pos,im,occ⟩,ac,dc⟩

theorem certificate_n12_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=1)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ∃ f : Sectors n 3 L, f.center=c ∧ AnyChartData G f ∧
      f.ordinaryShared.card=1 ∧ f.coreShared.card=2 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have occ : ∀ z∈f.triangular, Nonempty (Occurrence G f.center f.point z) := by
    intro z hz
    exact (mem_triangular G c f.point z).mp hz
  exact lift_n12_counts G f rc
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc)
    occ
    ((fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc).trans ac)
    ((fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc).trans dc)

theorem three_shared_run : ∀ T : Finset (ZMod 6),
    (T.filter (fun z=>z-1∈T)).card=3 →
      ∃ a : ZMod 6, T={a-1,a,a+1,a+2} := by decide +kernel

theorem finite_shift_n12 : ∀ a z : ZMod 6,
    a+z∈({a-1,a,a+1,a+2} : Finset (ZMod 6)) ↔
      z∈({5,0,1,2} : Finset (ZMod 6)) := by decide +kernel

theorem finite_n12_shared :
    (({5,0,1,2} : Finset (ZMod 6)).filter (fun z=>z-1∈({5,0,1,2} : Finset (ZMod 6))))=
      ({0,1,2} : Finset (ZMod 6)) := by decide +kernel

theorem normalize_n12_chart {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L) (df : AnyChartData G f)
    (ac : f.ordinaryShared.card=1) (dc : f.coreShared.card=2) :
    ∃ g : Sectors n 3 L, g.center=f.center ∧ AnyChartData G g ∧
      g.ordinaryShared.card=1 ∧ g.coreShared.card=2 ∧
      g.triangular=({5,0,1,2} : Finset (ZMod 6)) ∧ g.shared=({0,1,2} : Finset (ZMod 6)) := by
  classical
  have sc : f.shared.card=3 := by have h:=f.shared_card_split; omega
  obtain ⟨a,run⟩ := three_shared_run f.triangular sc
  let g := UpperOpenMathRotation.Sectors.shift f a
  have gt : g.triangular=({5,0,1,2} : Finset (ZMod 6)) := by
    ext z
    rw [UpperOpenMathRotation.Sectors.shift_mem_triangular,run]
    exact finite_shift_n12 a z
  refine ⟨g,rfl,shift_chart_data G f df a,?_,?_,gt,?_⟩
  · simpa only [g,UpperOpenMathRotation.Sectors.shift_ordinaryShared_card] using ac
  · simpa only [g,UpperOpenMathRotation.Sectors.shift_coreShared_card] using dc
  · change (g.triangular.filter (fun z=>z-1∈g.triangular))=_
    rw [gt]; exact finite_n12_shared

theorem normalized_n12_not_all_anti {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : Sectors n 3 L)
    (df : AnyChartData (fun a=>ofPredicate n L (tri a) hL (ht a)) f)
    (hc : f.center∈core n L) (ac : f.ordinaryShared.card=1)
    (ft : f.triangular=({5,0,1,2} : Finset (ZMod 6)))
    (fs : f.shared=({0,1,2} : Finset (ZMod 6))) :
    ¬∀ z∈f.coreShared, f.point z∈unmarkedFullTwoCapSet n L hL hn tri ht := by
  classical
  intro allAnti
  obtain ⟨o,oeq⟩ := card_eq_one.mp ac
  have om : o∈f.ordinaryShared := by rw [oeq]; simp
  have os : o∈({0,1,2} : Finset (ZMod 6)) := by rw [←fs]; exact f.ordinaryShared_subset om
  have cases : o=0∨o=1∨o=2 := by simpa only [mem_insert,mem_singleton] using os
  rcases cases with rfl|rfl|rfl
  · have h1 : (1 : ZMod 6)∈f.coreShared := by simp [Sectors.coreShared,fs,oeq] <;> decide
    have h2 : (2 : ZMod 6)∈f.coreShared := by simp [Sectors.coreShared,fs,oeq] <;> decide
    exact certificate_chart_anti_nonadjacent n L hL hn tri hi ht triples f df 1 h1
      (allAnti 1 h1) (by simpa using allAnti 2 h2)
  · have h0 : (0 : ZMod 6)∈f.coreShared := by simp [Sectors.coreShared,fs,oeq] <;> decide
    have h2 : (2 : ZMod 6)∈f.coreShared := by simp [Sectors.coreShared,fs,oeq] <;> decide
    have ord : OrdinaryAt n L (f.point 1) :=
      ((f.mem_ordinaryShared 1).mp (by rw [oeq]; simp)).2.2
    obtain ⟨a,w,ad,acenter,hw,aback,aprev,anext⟩ :=
      certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 0 h0 (allAnti 0 h0)
    obtain ⟨b,x,bd,bcenter,hx,bback,bprev,bnext⟩ :=
      certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 2 h2 (allAnti 2 h2)
    exact UpperOpenMathN13OrdinaryActual.canonical_ordinary_pair_impossible
      n L hL hn tri ht triples f a b df ad bd hc (by rw [ft]; simp) (by rw [ft]; simp)
      ord acenter bcenter w x hw hx aback bback (by simpa using aprev) (by simpa using bnext)
  · have h0 : (0 : ZMod 6)∈f.coreShared := by simp [Sectors.coreShared,fs,oeq] <;> decide
    have h1 : (1 : ZMod 6)∈f.coreShared := by simp [Sectors.coreShared,fs,oeq] <;> decide
    exact certificate_chart_anti_nonadjacent n L hL hn tri hi ht triples f df 0 h0
      (allAnti 0 h0) (by simpa using allAnti 1 h1)

theorem certificate_n12_has_nonanti_neighbor {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (c : Point) (hc : c∈core n L)
    (ac : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) c=1)
    (dc : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) c=2) :
    ∃ q∈core n L, {c,q}∈twoCoreEdges n L (fun a=>ofPredicate n L (tri a) hL (ht a)) ∧
      q∉unmarkedFullTwoCapSet n L hL hn tri ht := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  obtain ⟨f,fc,df,fo,fd⟩ := certificate_n12_chart n L hL hn tri hi ht c hc (triples c hc) ac dc
  obtain ⟨g,gf,dg,go,gd,gt,gs⟩ := normalize_n12_chart G f df fo fd
  have gc : g.center=c := gf.trans fc
  have notAll := normalized_n12_not_all_anti n L hL hn tri hi ht triples g dg
    (by rw [gc]; exact hc) go gt gs
  push_neg at notAll
  obtain ⟨z,hz,notA⟩ := notAll
  have qcore := certificate_chart_core_endpoint n L hL tri ht g dg z hz
  have he : ({g.center,g.point z} : Edge)∈twoCoreEdges n L G := by
    have him : ({g.center,g.point z} : Edge)∈g.coreShared.image
        (fun z=>({g.center,g.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
    rw [dg.core_image] at him
    exact (mem_filter.mp him).1
  exact ⟨g.point z,qcore,by simpa only [gc] using he,notA⟩

theorem certificate_n12_anti_degree_le_one {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (c : Point) (hc : c∈core n L)
    (ac : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) c=1)
    (dc : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) c=2) :
    degreeFrom n L (fun a=>ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) c≤1 := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  change ordinaryDegree n L G c=1 at ac
  change coreDegree n L G c=2 at dc
  let E := (twoCoreEdges n L G).filter fun e=>c∈e
  let X := E.filter fun e=>(e∩A).Nonempty
  obtain ⟨q,hq,edge,notA⟩ := certificate_n12_has_nonanti_neighbor n L hL hn tri hi ht triples c hc ac dc
  have cnot : c∉A := by
    intro h
    have h2 := (mem_filter.mp h).2.1
    change ordinaryDegree n L G c=2 at h2
    omega
  have inE : ({c,q} : Edge)∈E := mem_filter.mpr ⟨edge,by simp⟩
  have outX : ({c,q} : Edge)∉X := by
    intro h
    obtain ⟨p,hp⟩ := (mem_filter.mp h).2
    obtain ⟨hpE,hpA⟩ := mem_inter.mp hp
    rcases mem_insert.mp hpE with he|he
    · exact cnot (by simpa only [he] using hpA)
    · exact notA (by simpa only [mem_singleton.mp he] using hpA)
  have proper : X⊂E := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,by
    intro he
    rw [he] at outX
    exact outX inE⟩
  have lt := card_lt_card proper
  have ec : E.card=2 := dc
  have eq : degreeFrom n L G A c=X.card := by
    apply congrArg Finset.card
    ext e
    simp only [X,E,mem_filter,and_assoc]
  rw [ec] at lt
  rw [eq]
  omega

#print axioms certificate_n12_anti_degree_le_one
end Kobon.UpperOpenMathN12Recipient
