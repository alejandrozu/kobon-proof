import Kobon.UpperOpenMathN13ActualChart
import Kobon.UpperOpenMathN13Mirror
import Kobon.UpperOpenMathN13Antipodal
import Kobon.UpperOpenMathN13Separated
import Kobon.UpperOpenMathN13Support
import Kobon.UpperOpenMathN13ExtractionHelpers
import Kobon.UpperOpenMathN13OrdinaryActual

namespace Kobon.UpperOpenMathN13NoDouble
open Cells FanGeometry UpperFan UpperVertexBudget UpperCoreExtraction
  UpperOpenMathAntipodalAdjacency UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalFullNeighborPair UpperOpenMathN13ActualChart
  UpperOpenMathN13Mirror UpperOpenMathN13ExtractionHelpers Finset
set_option maxHeartbeats 2000000

section
variable {α : Type*} [Fintype α]
variable (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α → Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a))
  (triples : ∀ p∈core n L, (supports n L p).card=3)
  (f : Sectors n 3 L)
  (df : AnyChartData (fun a=>ofPredicate n L (tri a) hL (ht a)) f)

include hL hn tri hi ht triples f df

private theorem endpoint_triple (z : ZMod 6) (hz : z∈f.coreShared) :
    (supports n L (f.point z)).card=3 :=
  triples _ (certificate_chart_core_endpoint n L hL tri ht f df z hz)

private theorem case_core02 (s0 : (0 : ZMod 6)∈f.triangular)
    (s1 : (1 : ZMod 6)∈f.triangular)
    (h0 : (0 : ZMod 6)∈f.coreShared) (h1 : (1 : ZMod 6)∈f.coreShared)
    (h2 : (2 : ZMod 6)∈f.coreShared) (ord3 : OrdinaryAt n L (f.point 3))
    (q0 : f.point 0∈UpperOpenMathAntipodalAdjacency.unmarkedFullTwoCapSet n L hL hn tri ht)
    (q2 : f.point 2∈UpperOpenMathAntipodalAdjacency.unmarkedFullTwoCapSet n L hL hn tri ht) : False := by
  obtain ⟨g,w,dg,gc,hw,gp,gr,gl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 0 h0 q0
  obtain ⟨k,x,dk,kc,hx,kp,kr,kl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 2 h2 q2
  have rc := endpoint_triple n L hL hn tri hi ht triples f df 1 h1
  have go := antipodal_previous_ordinary _ g dg w hw (by simpa only [gr,zero_add] using rc)
  have ko : OrdinaryAt n L (k.point (x-1)) := by rw [kr]; exact ord3
  have capne := UpperOpenMathN13Support.certificate_selected_core_cap_ne n L hL tri ht f df 1
    (by simpa using s0) s1 rc
  exact UpperOpenMathN13Separated.separated_core_pair_impossible hL hn f g k s0 s1 rc
    df.injective (df.noncentral 3) (df.positive 0) (by simpa using df.positive 1) capne
    dg.triangular_eq w gc gp (by simpa using gr) go
    dk.triangular_eq x kc kp (by simpa using kr) (by simpa using kl) ko

private theorem case_opposite_one (s0 : (0 : ZMod 6)∈f.triangular)
    (s1 : (1 : ZMod 6)∈f.triangular) (s2 : (2 : ZMod 6)∈f.triangular)
    (h2 : (2 : ZMod 6)∈f.coreShared) (h3 : (3 : ZMod 6)∈f.coreShared)
    (ord1 : OrdinaryAt n L (f.point 1))
    (q3 : f.point 3∈unmarkedFullTwoCapSet n L hL hn tri ht) : False := by
  obtain ⟨g,w,dg,gc,hw,gp,gr,gl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 3 h3 q3
  have rc := endpoint_triple n L hL hn tri hi ht triples f df 2 h2
  have go := antipodal_next_ordinary _ g dg w hw (by rw [gl]; exact rc)
  have hi1 : 0-(-w-1)=w+1 := by ring
  have hi2 : 0-(-w-2)=w+2 := by ring
  exact UpperOpenMathN13Antipodal.opposite_pair_impossible hL f (mirror g 0) s0 s1 s2
    ord1 rc (df.noncentral 0) (df.noncentral 2) df.injective
    (mirror_full g 0 dg.triangular_eq) (-w) gc
    (by simpa only [mirror_point,zero_sub,neg_neg] using gp)
    (by rw [mirror_point,hi1]; exact gl)
    (by simpa only [mirror_point,hi2] using go)

private theorem case_opposite_two (s0 : (0 : ZMod 6)∈f.triangular)
    (s1 : (1 : ZMod 6)∈f.triangular) (s2 : (2 : ZMod 6)∈f.triangular)
    (h0 : (0 : ZMod 6)∈f.coreShared) (h1 : (1 : ZMod 6)∈f.coreShared)
    (ord2 : OrdinaryAt n L (f.point 2))
    (q0 : f.point 0∈unmarkedFullTwoCapSet n L hL hn tri ht) : False := by
  obtain ⟨g,w,dg,gc,hw,gp,gr,gl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 0 h0 q0
  have rc := endpoint_triple n L hL hn tri hi ht triples f df 1 h1
  have go := antipodal_previous_ordinary _ g dg w hw (by simpa only [gr,zero_add] using rc)
  let F := mirror f 3
  have F0 : F.point 0=f.point 3 := by change f.point (3-0)=f.point 3; congr 1
  have F1 : F.point 1=f.point 2 := by change f.point (3-1)=f.point 2; congr 1
  have F2 : F.point 2=f.point 1 := by change f.point (3-2)=f.point 1; congr 1
  have F3 : F.point 3=f.point 0 := by change f.point (3-3)=f.point 0; congr 1
  apply UpperOpenMathN13Antipodal.opposite_pair_impossible hL F g
    (by rw [mirror_mem_triangular f 3 0]; exact s2)
    (by rw [mirror_mem_triangular f 3 1]; exact s1)
    (by rw [mirror_mem_triangular f 3 2]; exact s0)
    (by rw [F1]; exact ord2) (by rw [F2]; exact rc)
    (by rw [F0]; exact df.noncentral 3) (by rw [F2]; exact df.noncentral 1)
    (mirror_injective f 3 df.injective) dg.triangular_eq w
    (by rw [F3]; exact gc) gp (by rw [F2]; simpa using gr) go

private theorem case_ordinary02 (hc : f.center∈core n L)
    (s0 : (0 : ZMod 6)∈f.triangular) (s1 : (1 : ZMod 6)∈f.triangular)
    (h0 : (0 : ZMod 6)∈f.coreShared) (h2 : (2 : ZMod 6)∈f.coreShared)
    (ord1 : OrdinaryAt n L (f.point 1))
    (q0 : f.point 0∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (q2 : f.point 2∈unmarkedFullTwoCapSet n L hL hn tri ht) : False := by
  obtain ⟨g,w,dg,gc,hw,gp,gr,gl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 0 h0 q0
  obtain ⟨k,x,dk,kc,hx,kp,kr,kl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 2 h2 q2
  exact UpperOpenMathN13OrdinaryActual.canonical_ordinary_pair_impossible n L hL hn tri ht triples
    f g k df dg dk hc s0 s1 ord1 gc kc w x hw hx gp kp
    (by simpa using gr) (by simpa using kl)

private theorem case_core13 (s1 : (1 : ZMod 6)∈f.triangular)
    (s2 : (2 : ZMod 6)∈f.triangular)
    (h1 : (1 : ZMod 6)∈f.coreShared) (h2 : (2 : ZMod 6)∈f.coreShared)
    (h3 : (3 : ZMod 6)∈f.coreShared) (ord0 : OrdinaryAt n L (f.point 0))
    (q1 : f.point 1∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (q3 : f.point 3∈unmarkedFullTwoCapSet n L hL hn tri ht) : False := by
  obtain ⟨g,w,dg,gc,hw,gp,gr,gl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 3 h3 q3
  obtain ⟨k,x,dk,kc,hx,kp,kr,kl⟩ := certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df 1 h1 q1
  have rc := endpoint_triple n L hL hn tri hi ht triples f df 2 h2
  have go := antipodal_next_ordinary _ g dg w hw (by rw [gl]; exact rc)
  have ko : OrdinaryAt n L (k.point (x+1)) := by simpa only [kl,sub_self] using ord0
  have capne := UpperOpenMathN13Support.certificate_selected_core_cap_ne n L hL tri ht f df 2
    (by simpa using s1) s2 rc
  let F := mirror f 3
  have F0 : F.point 0=f.point 3 := by change f.point (3-0)=f.point 3; congr 1
  have F1 : F.point 1=f.point 2 := by change f.point (3-1)=f.point 2; congr 1
  have F2 : F.point 2=f.point 1 := by change f.point (3-2)=f.point 1; congr 1
  have F3 : F.point 3=f.point 0 := by change f.point (3-3)=f.point 0; congr 1
  have hn0 : (3 : ZMod 6)-0-1=2 := by decide
  have hn1 : (3 : ZMod 6)-0=3 := by decide
  have hn2 : (3 : ZMod 6)-1-1=1 := by decide
  have hn3 : (3 : ZMod 6)-1=2 := by decide
  have negative0 : areaDet F.center (F.point 0) (F.point 1)<0 := by
    change areaDet (mirror f 3).center ((mirror f 3).point 0) ((mirror f 3).point (0+1))<0
    rw [mirror_area f 3 0,hn0,hn1]
    simpa using neg_neg_of_pos (df.positive 2)
  have negative1 : areaDet F.center (F.point 1) (F.point 2)<0 := by
    change areaDet (mirror f 3).center ((mirror f 3).point 1) ((mirror f 3).point (1+1))<0
    rw [mirror_area f 3 1,hn2,hn3]
    simpa using neg_neg_of_pos (df.positive 1)
  have H1 (a : ZMod 6) : 0-(-a-1)=a+1 := by ring
  have H2 (a : ZMod 6) : 0-(-a-2)=a+2 := by ring
  have HP (a : ZMod 6) : 0-(-a+1)=a-1 := by ring
  apply UpperOpenMathN13Separated.separated_core_pair_impossible_negative hL hn F
    (mirror g 0) (mirror k 0)
    (by rw [mirror_mem_triangular f 3 0,hn0]; exact s2)
    (by rw [mirror_mem_triangular f 3 1,hn2]; exact s1)
    (by rw [F1]; exact rc) (mirror_injective f 3 df.injective)
    (by rw [F3]; exact df.noncentral 0) negative0 negative1
    (by change f.opposite (3-0-1)≠f.opposite (3-1-1); rw [hn0,hn2]; exact capne.symm)
    (mirror_full g 0 dg.triangular_eq) (-w)
    (by rw [F0]; exact gc)
    (by simpa only [F,mirror_center,mirror_point,zero_sub,neg_neg] using gp)
    (by rw [F1,mirror_point,H1]; exact gl)
    (by simpa only [mirror_point,H2] using go)
    (mirror_full k 0 dk.triangular_eq) (-x)
    (by rw [F2]; exact kc)
    (by simpa only [F,mirror_center,mirror_point,zero_sub,neg_neg] using kp)
    (by rw [F3]; simpa only [mirror_point,H1,sub_self] using kl)
    (by rw [F1,mirror_point,HP]; exact kr)
    (by simpa only [mirror_point,H1] using ko)

private theorem case_ordinary13 (hc : f.center∈core n L)
    (s1 : (1 : ZMod 6)∈f.triangular) (s2 : (2 : ZMod 6)∈f.triangular)
    (h1 : (1 : ZMod 6)∈f.coreShared) (h3 : (3 : ZMod 6)∈f.coreShared)
    (ord2 : OrdinaryAt n L (f.point 2))
    (q1 : f.point 1∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (q3 : f.point 3∈unmarkedFullTwoCapSet n L hL hn tri ht) : False := by
  let F := UpperOpenMathRotation.Sectors.shift f 1
  have FD := shift_chart_data _ f df 1
  have S0 : (0 : ZMod 6)∈F.triangular := by
    rw [UpperOpenMathRotation.Sectors.shift_mem_triangular]; simpa using s1
  have S1 : (1 : ZMod 6)∈F.triangular := by
    rw [UpperOpenMathRotation.Sectors.shift_mem_triangular]; simpa using s2
  have C0 : (0 : ZMod 6)∈F.coreShared := by
    rw [UpperOpenMathRotation.Sectors.shift_mem_coreShared]; simpa using h1
  have C2 : (2 : ZMod 6)∈F.coreShared := by
    rw [UpperOpenMathRotation.Sectors.shift_mem_coreShared]; exact h3
  exact case_ordinary02 n L hL hn tri hi ht triples F FD hc S0 S1 C0 C2
    (by change OrdinaryAt n L (f.point (1+1)); exact ord2)
    (by simpa only [F,UpperOpenMathRotation.Sectors.shift_point,add_zero] using q1)
    (by change f.point (1+2)∈_; exact q3)

/-- Every actual one-cap/three-core triple recipient has at most one
    unmarked full antipodal two-cap neighbor. All six finite positions are
    discharged by real support continuation and actual empty-cell tests. -/
theorem certificate_chart_no_two_anti
    (hc : f.center∈core n L)
    (sharedRun : f.shared=({0,1,2,3} : Finset (ZMod 6)))
    (ordinarycard1 : f.ordinaryShared.card=1)
    (z v : ZMod 6) (hz : z∈f.coreShared) (hv : v∈f.coreShared)
    (qa : f.point z∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (ra : f.point v∈unmarkedFullTwoCapSet n L hL hn tri ht) (hne : z≠v) : False := by
  classical
  obtain ⟨o,ordEq⟩ := card_eq_one.mp ordinarycard1
  let A : Finset (ZMod 6) := {z,v}
  have Acore (w : ZMod 6) (hw : w∈A) : w∈f.coreShared := by
    simp only [A,mem_insert,mem_singleton] at hw
    rcases hw with rfl|rfl
    · exact hz
    · exact hv
  have Aanti (w : ZMod 6) (hw : w∈A) : f.point w∈unmarkedFullTwoCapSet n L hL hn tri ht := by
    simp only [A,mem_insert,mem_singleton] at hw
    rcases hw with rfl|rfl
    · exact qa
    · exact ra
  have Asub : A⊆({0,1,2,3} : Finset (ZMod 6)) := by
    intro w hw
    rw [←sharedRun]
    exact (mem_sdiff.mp (Acore w hw)).1
  have Acard : A.card=2 := by simp [A,hne]
  have omem : o∈f.ordinaryShared := by rw [ordEq]; simp
  have orun : o∈({0,1,2,3} : Finset (ZMod 6)) := by
    rw [←sharedRun]
    exact f.ordinaryShared_subset omem
  have onot : o∉A := by
    intro ho
    exact (mem_sdiff.mp (Acore o ho)).2 omem
  have nonadj : ∀ w∈A,w+1∉A := by
    intro w hw hnext
    exact certificate_chart_anti_nonadjacent n L hL hn tri hi ht triples f df w
      (Acore w hw) (Aanti w hw) (Aanti (w+1) hnext)
  have coreLab (w : ZMod 6) (hrun : w∈({0,1,2,3} : Finset (ZMod 6))) (hwo : w≠o) : w∈f.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by rw [sharedRun]; exact hrun,?_⟩
    rw [ordEq]
    simpa using hwo
  have ord : OrdinaryAt n L (f.point o) := ((f.mem_ordinaryShared o).mp omem).2.2
  have sel (w : ZMod 6) (hrun : w∈({0,1,2,3} : Finset (ZMod 6))) : w∈f.triangular := by
    have hh : w∈f.shared := by rw [sharedRun]; exact hrun
    exact (mem_filter.mp hh).1
  have s0 := sel 0 (by decide)
  have s1 := sel 1 (by decide)
  have s2 := sel 2 (by decide)
  rcases UpperOpenMathN13Cases.two_nonadjacent_core_positions A o Asub Acard orun onot nonadj with
    ⟨pair,ordinary⟩|⟨pair,ordinary⟩|⟨pair,ordinary⟩
  · have q0 := Aanti 0 (by rw [pair]; simp)
    have q2 := Aanti 2 (by rw [pair]; simp)
    rcases ordinary with rfl|rfl
    · exact case_ordinary02 n L hL hn tri hi ht triples f df hc s0 s1
        (coreLab 0 (by decide) (by decide)) (coreLab 2 (by decide) (by decide)) ord q0 q2
    · exact case_core02 n L hL hn tri hi ht triples f df s0 s1
        (coreLab 0 (by decide) (by decide)) (coreLab 1 (by decide) (by decide))
        (coreLab 2 (by decide) (by decide)) ord q0 q2
  · have q1 := Aanti 1 (by rw [pair]; simp)
    have q3 := Aanti 3 (by rw [pair]; simp)
    rcases ordinary with rfl|rfl
    · exact case_core13 n L hL hn tri hi ht triples f df s1 s2
        (coreLab 1 (by decide) (by decide)) (coreLab 2 (by decide) (by decide))
        (coreLab 3 (by decide) (by decide)) ord q1 q3
    · exact case_ordinary13 n L hL hn tri hi ht triples f df hc s1 s2
        (coreLab 1 (by decide) (by decide)) (coreLab 3 (by decide) (by decide)) ord q1 q3
  · have q0 := Aanti 0 (by rw [pair]; simp)
    have q3 := Aanti 3 (by rw [pair]; simp)
    rcases ordinary with rfl|rfl
    · exact case_opposite_one n L hL hn tri hi ht triples f df s0 s1 s2
        (coreLab 2 (by decide) (by decide)) (coreLab 3 (by decide) (by decide)) ord q3
    · exact case_opposite_two n L hL hn tri hi ht triples f df s0 s1 s2
        (coreLab 0 (by decide) (by decide)) (coreLab 1 (by decide) (by decide)) ord q0

#print axioms certificate_chart_no_two_anti
end
end Kobon.UpperOpenMathN13NoDouble



