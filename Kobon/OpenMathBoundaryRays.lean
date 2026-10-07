import Kobon.OpenMathSimpleBoundary
import Kobon.OpenMathBoundaryNormals

/-! Terminal vertices extracted from sorted actual line intersections have
actual forward rays avoiding every transverse old line.  This supplies the
geometric sign input for exact exterior normal-sector counting. -/
namespace Kobon.OpenMathBoundaryRays
open Cells FanGeometry UpperVertexBudget UpperEdgeInventory OpenMathSimpleBoundary
  OpenMathBoundaryNormals Exterior Finset
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable def coordinateRay (l : Line ℝ) (s : ℝ) : Point :=
  if l.b=0 then (0,s) else (s,-l.a/l.b*s)

theorem coordinateRay_projection (l : Line ℝ) (s : ℝ) :
    projection l (coordinateRay l s)=0 := by
  by_cases hb : l.b=0
  · simp [coordinateRay,hb,projection]
  · dsimp [coordinateRay,projection]
    rw [if_neg hb]
    dsimp
    field_simp
    ring

theorem ray_coordinate (l : Line ℝ) (p : Point) (s t : ℝ) :
    coordinate l (rayPoint p (coordinateRay l s) t)=coordinate l p+t*s := by
  unfold coordinate coordinateRay rayPoint
  split_ifs <;> dsimp <;> ring

theorem coordinateRay_ne_zero (l : Line ℝ) {s : ℝ} (hs : s≠0) :
    coordinateRay l s≠(0,0) := by
  unfold coordinateRay
  split_ifs
  · intro he
    exact hs (congrArg Prod.snd he)
  · intro he
    exact hs (congrArg Prod.fst he)

theorem coordinateRay_transverse (l r : Line ℝ) {s : ℝ} (hs : s≠0)
    (hd : det l r≠0) : projection r (coordinateRay l s)≠0 := by
  by_cases hb : l.b=0
  · have hdet : det l r=l.a*r.b := by simp [det,hb]
    have hr : r.b≠0 := by intro hr; simp [hdet,hr] at hd
    simp [coordinateRay,hb,projection,mul_ne_zero hr hs]
  · have he : l.b*projection r (coordinateRay l s)= -(det l r)*s := by
      dsimp [coordinateRay,projection]
      rw [if_neg hb]
      dsimp [det]
      field_simp
      ring
    intro hz
    rw [hz,mul_zero] at he
    exact (mul_ne_zero (neg_ne_zero.mpr hd) hs) he.symm

theorem ray_avoids_of_extreme (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (i : Fin n) (p : Point) (hpi : p∈onLine n L i)
    (s : ℝ) (hs : s=-1 ∨ s=1)
    (hext : ∀ q∈onLine n L i,s*(coordinate (L i) q-coordinate (L i) p)≤0) :
    ForwardAvoids n L p (coordinateRay (L i) s) := by
  intro r hr t ht hz
  let q := rayPoint p (coordinateRay (L i) s) t
  have hqi : affineEval (L i) q=0 := by
    rw [ray_eval,(mem_filter.mp hpi).2,coordinateRay_projection,mul_zero,add_zero]
  have hir : i≠r := by
    intro he
    rw [← he,(mem_filter.mp hpi).2] at hr
    exact hr rfl
  have hd := noParallel_any n L hp i r i.isLt r.isLt (fun h => hir (Fin.ext h))
  have hqeq : intersection (L i) (L r)=q :=
    (intersection_eq_iff n L hp i r hir q).mpr ⟨hqi,hz⟩
  have hqv : q∈vertices n L := by
    rw [← hqeq]
    exact mem_image.mpr ⟨(i,r),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hir⟩,rfl⟩
  have hb := hext q (mem_filter.mpr ⟨hqv,hqi⟩)
  have hc : coordinate (L i) q=coordinate (L i) p+t*s := ray_coordinate _ _ _ _
  rw [hc] at hb
  rcases hs with rfl|rfl <;> nlinarith

/-- An actual terminal endpoint supplies a nonzero tangent direction whose
forward ray avoids all other old intersections, with exact transverse signs. -/
theorem terminal_outward_signs (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (i : Fin n) {p : Point} (ht : p∈lineTerminals n L i) :
    ∃ d : Point, d≠(0,0) ∧ projection (L i) d=0 ∧
      ForwardAvoids n L p d ∧ TerminalSigns n L p d := by
  classical
  have hpi := terminal_mem_onLine n L hp hn i ht
  obtain hmin|hmax := terminal_extreme_coordinate n L hp hn i ht
  · let d := coordinateRay (L i) (-1)
    have havoid : ForwardAvoids n L p d := ray_avoids_of_extreme n L hp hn i p hpi
      (-1) (Or.inl rfl) (by intro q hq; have := hmin q hq; linarith)
    refine ⟨d,coordinateRay_ne_zero _ (by norm_num),coordinateRay_projection _ _,havoid,?_⟩
    apply terminalSigns_of_avoids n L p d havoid
    intro r hr
    have hir : i≠r := by
      intro he
      rw [← he,(mem_filter.mp hpi).2] at hr
      exact hr rfl
    exact coordinateRay_transverse _ _ (by norm_num)
      (noParallel_any n L hp i r i.isLt r.isLt (fun h => hir (Fin.ext h)))
  · let d := coordinateRay (L i) 1
    have havoid : ForwardAvoids n L p d := ray_avoids_of_extreme n L hp hn i p hpi
      1 (Or.inr rfl) (by intro q hq; have := hmax q hq; linarith)
    refine ⟨d,coordinateRay_ne_zero _ (by norm_num),coordinateRay_projection _ _,havoid,?_⟩
    apply terminalSigns_of_avoids n L p d havoid
    intro r hr
    have hir : i≠r := by
      intro he
      rw [← he,(mem_filter.mp hpi).2] at hr
      exact hr rfl
    exact coordinateRay_transverse _ _ (by norm_num)
      (noParallel_any n L hp i r i.isLt r.isLt (fun h => hir (Fin.ext h)))

#print axioms ray_avoids_of_extreme
#print axioms terminal_outward_signs
end Kobon.OpenMathBoundaryRays
