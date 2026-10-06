import Kobon.UpperOpenMathN13SupportExtreme
import Kobon.UpperOpenMathTwoCapNeighborRigidity
import Kobon.UpperOpenMathUnmarkedCrossResources

namespace Kobon.UpperOpenMathN13ActualSupportExtreme
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathAntipodalAdjacency
  UpperOpenMathN13ActualChart UpperOpenMathAntipodalFullNeighborPair
  UpperOpenMathCoreComponents Finset
set_option maxHeartbeats 1000000

/-- In any finite closed shared-core set, an actual N13 vertex with an A0
    neighbor cannot maximize an affine functional injective on that set. -/
theorem certificate_n13_with_anti_not_max {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ac : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1)
    (dc : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3)
    (c : Point) (hcA : c∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (edgepc : {p,c}∈twoCoreEdges n L (fun a=>ofPredicate n L (tri a) hL (ht a)))
    (P : Finset Point) (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P)
    (pp : p∈P) (W : Line ℝ) (inj : Set.InjOn (affineEval W) (↑P : Set Point)) :
    ¬(∀ q∈P, affineEval W q≤affineEval W p) := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have cne : c≠p := by
    intro he
    have ca := (mem_filter.mp hcA).2.1
    rw [he] at ca
    omega
  obtain ⟨f,fp,df,fac,fdc⟩ := certificate_n13_chart n L hL hn tri hi ht p hp (triples p hp) ac dc
  obtain ⟨g,gf,dg,gac,gdc,gt,gs⟩ := normalize_n13_chart G f df fac fdc
  have gp : g.center=p := gf.trans fp
  obtain ⟨z,hz,hzc⟩ := UpperOpenMathTwoCapNeighborRigidity.reverse_label_of_image G g dg.core_image
    c (by rw [gp]; exact cne) (by rwa [gp])
  have escape := UpperOpenMathN13SupportExtreme.certificate_n13_anti_not_max n L hL hn tri hi ht triples
    g dg gs gac z hz (by simpa only [hzc] using hcA) P closed (by rw [gp]; exact pp) W inj
  simpa only [gp] using escape

/-- The same actual escape in the recipient-degree form used by component
    charging: one or more A0 incidences excludes an injective affine maximum. -/
theorem certificate_n13_positive_anti_degree_not_max {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ac : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1)
    (dc : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3)
    (positive : 1≤UpperOpenMathUnmarkedCrossResources.degreeFrom n L
      (fun a=>ofPredicate n L (tri a) hL (ht a)) (unmarkedFullTwoCapSet n L hL hn tri ht) p)
    (P : Finset Point) (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P)
    (pp : p∈P) (W : Line ℝ) (inj : Set.InjOn (affineEval W) (↑P : Set Point)) :
    ¬(∀ q∈P, affineEval W q≤affineEval W p) := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  let E := (twoCoreEdges n L G).filter (fun e=>p∈e ∧ (e∩A).Nonempty)
  change 1≤E.card at positive
  have nonempty : E.Nonempty := card_pos.mp (by omega)
  obtain ⟨e,he⟩ := nonempty
  obtain ⟨he,hpe,c,hc⟩ := mem_filter.mp he
  obtain ⟨hce,hcA⟩ := mem_inter.mp hc
  have ne : p≠c := by
    intro eq
    have ca := (mem_filter.mp hcA).2.1
    rw [←eq] at ca
    omega
  have pair : e=({p,c} : Edge) := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro q hq
      rcases mem_insert.mp hq with hq|hq
      · simpa only [hq] using hpe
      · simpa only [mem_singleton.mp hq] using hce
    · rw [card_pair ne,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
  exact certificate_n13_with_anti_not_max n L hL hn tri hi ht triples p hp ac dc c hcA
    (by simpa only [pair] using he) P closed pp W inj

#print axioms certificate_n13_positive_anti_degree_not_max
#print axioms certificate_n13_with_anti_not_max
end Kobon.UpperOpenMathN13ActualSupportExtreme

