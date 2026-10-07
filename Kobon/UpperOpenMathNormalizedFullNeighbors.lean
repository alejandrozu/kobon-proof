import Kobon.UpperOpenMathMarkedFanShapes

/-! A normalized two-cap triple core cannot have full triangular fans at
both of its shared-core neighbors. The obstruction is the actual antipodal
cap axis at the original core, without a cap hypothesis at the two others. -/
namespace Kobon.UpperOpenMathNormalizedFullNeighbors
open Cells FanGeometry UpperFan UpperOpenMathTripleCharts Finset
set_option maxHeartbeats 1000000

theorem normalized_full_neighbors_impossible {α : Type*} [Fintype α]
    (G : α → TriangleGeometry) {n : ℕ} {L : ℕ → Line ℝ} (hL : NoParallel n L)
    (f g h : UpperFan.Sectors n 3 L) (df : NormalizedData G f)
    (gfull : g.triangular=univ) (hfull : h.triangular=univ)
    (gnc : ∀ z, g.point z≠g.center)
    (w x : ZMod (2*3))
    (gc : g.center=f.point 1) (gp : g.point w=f.center)
    (gprev : g.point (w-1)=f.point 2) (gnext : g.point (w+1)=f.point 0)
    (hc : h.center=f.point 2) (hp : h.point x=f.center)
    (hprev : h.point (x-1)=f.point 3) (hnext : h.point (x+1)=f.point 1) : False := by
  classical
  have f0 : OrdinaryAt n L (f.point 0) :=
    ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
  have f3 : OrdinaryAt n L (f.point 3) :=
    ((f.mem_ordinaryShared 3).mp (by rw [df.ordinary_eq]; simp)).2.2
  have gcap : w+1∈g.ordinaryShared :=
    (g.mem_ordinaryShared (w+1)).mpr ⟨by rw [gfull]; simp,by rw [gfull]; simp,gnext.symm ▸ f0⟩
  have hcap : x-1∈h.ordinaryShared :=
    (h.mem_ordinaryShared (x-1)).mpr ⟨by rw [hfull]; simp,by rw [hfull]; simp,hprev.symm ▸ f3⟩
  let a := UpperOpenMathRotation.Sectors.shift g (w-2)
  let b := UpperOpenMathRotation.Sectors.shift h (x-1)
  have addg1 : w-2+(1 : ZMod (2*3))=w-1 := by ring
  have addg2 : w-2+(2 : ZMod (2*3))=w := by ring
  have addg3 : w-2+(3 : ZMod (2*3))=w+1 := by ring
  have addh0 : x-1+(0 : ZMod (2*3))=x-1 := by ring
  have addh1 : x-1+(1 : ZMod (2*3))=x := by ring
  have addh2 : x-1+(2 : ZMod (2*3))=x+1 := by ring
  have acap : (3 : ZMod (2*3))∈a.ordinaryShared := by
    apply (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared g (w-2) 3).mpr
    simpa only [addg3] using gcap
  have bcap : (0 : ZMod (2*3))∈b.ordinaryShared := by
    apply (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared h (x-1) 0).mpr
    simpa only [addh0] using hcap
  exact UpperOpenMathTwoCapCycle.three_two_cap_fans_incompatible hL a b f acap bcap
    (by simpa only [a,b,UpperOpenMathRotation.Sectors.shift_center,UpperOpenMathRotation.Sectors.shift_point,addg1,hc] using gprev.symm)
    (by simpa only [a,b,UpperOpenMathRotation.Sectors.shift_center,UpperOpenMathRotation.Sectors.shift_point,addh2,gc] using hnext)
    (by simpa only [b,UpperOpenMathRotation.Sectors.shift_point,addh1] using hp)
    (by simpa only [a,UpperOpenMathRotation.Sectors.shift_point,addg2] using gp.symm)
    (by simpa only [a,UpperOpenMathRotation.Sectors.shift_point,addg3] using gnext.symm)
    (by simpa only [b,UpperOpenMathRotation.Sectors.shift_point,addh0] using hprev.symm)
    (by simpa only [a,UpperOpenMathRotation.Sectors.shift_center,UpperOpenMathRotation.Sectors.shift_point,addg1] using gnc (w-1))
    df.noncentral

#print axioms normalized_full_neighbors_impossible
end Kobon.UpperOpenMathNormalizedFullNeighbors
