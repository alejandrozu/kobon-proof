import Kobon.UpperOpenMathN13ActualChart
import Kobon.UpperOpenMathN13NoDouble
import Kobon.UpperOpenMathTwoCapNeighborRigidity

/-! Actual extraction of the no-double-antipodal-recipient property. -/
namespace Kobon.UpperOpenMathN13ActualNoDouble
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathCapHeavyTriples
  UpperOpenMathAntipodalAdjacency UpperOpenMathN13ActualChart
  UpperOpenMathAntipodalFullNeighborPair Finset
set_option maxHeartbeats 1000000

theorem certificate_n13_no_two_anti_neighbors {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ac : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1)
    (dc : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3)
    (c d : Point)
    (hcA : c∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (hdA : d∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (edgepc : {p,c}∈twoCoreEdges n L (fun a=>ofPredicate n L (tri a) hL (ht a)))
    (edgepd : {p,d}∈twoCoreEdges n L (fun a=>ofPredicate n L (tri a) hL (ht a))) : c=d := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have cne : c≠p := by
    intro he
    have ca := (mem_filter.mp hcA).2.1
    rw [he] at ca
    omega
  have dne : d≠p := by
    intro he
    have da := (mem_filter.mp hdA).2.1
    rw [he] at da
    omega
  obtain ⟨f,fp,df,fac,fdc⟩ := certificate_n13_chart n L hL hn tri hi ht p hp (triples p hp) ac dc
  obtain ⟨g,gf,dg,gac,gdc,gt,gs⟩ := normalize_n13_chart G f df fac fdc
  have gp : g.center=p := gf.trans fp
  obtain ⟨z,hz,hzc⟩ := UpperOpenMathTwoCapNeighborRigidity.reverse_label_of_image G g dg.core_image
    c (by rw [gp]; exact cne) (by rwa [gp])
  obtain ⟨v,hv,hvd⟩ := UpperOpenMathTwoCapNeighborRigidity.reverse_label_of_image G g dg.core_image
    d (by rw [gp]; exact dne) (by rwa [gp])
  by_contra hne
  have zv : z≠v := by
    intro he
    apply hne
    rw [←hzc,←hvd,he]
  exact UpperOpenMathN13NoDouble.certificate_chart_no_two_anti n L hL hn tri hi ht triples
    g dg (by rw [gp]; exact hp) gs gac z v hz hv
    (by simpa only [hzc] using hcA) (by simpa only [hvd] using hdA) zv

#print axioms certificate_n13_no_two_anti_neighbors
end Kobon.UpperOpenMathN13ActualNoDouble
