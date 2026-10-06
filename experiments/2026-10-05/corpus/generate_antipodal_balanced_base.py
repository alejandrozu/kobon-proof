"""Reuse the checked geometric chain with only the needed selected sectors.

The generated Lean proof replaces the full neighbor by actual NormalizedData;
every selected-cap fact and original occurrence is independently kernel proved.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
source=(ROOT/'Kobon/UpperOpenMathAntipodalAdjacency.lean').read_text(encoding='utf-8')
body=source[source.index('theorem normalized_pair_incompatible'):source.index('theorem charts_neighbor_matching')]
body=body.replace('theorem normalized_pair_incompatible','theorem normalized_right_pair_incompatible')
body=body.replace('(dg : AntipodalData','(dg : NormalizedData')
body=body.replace('  have fo0 :','  have gs (z : ZMod 6) (hz : z∈({0,1,2,3,5} : Finset (ZMod 6))) : z∈g.triangular :=\n    normalized_selected G g dg z hz\n  have fo0 :',1)
body=body.replace('cap_eq_at_ordinary g dg.triangular_eq 0 go0','cap_eq_selected g 0 (by simpa using gs 5 (by decide)) (gs 0 (by decide)) go0')
for z in [0,1,2,3,5]:
    body=body.replace(f'cap_left g dg.triangular_eq {z}',f'cap_left_at g {z} (gs {z} (by decide))')
    body=body.replace(f'cap_right g dg.triangular_eq {z}',f'cap_right_at g {z} (gs {z} (by decide))')
    body=body.replace(f'cap_avoids g dg.triangular_eq {z}',f'cap_avoids_at g {z} (gs {z} (by decide))')
body=body.replace('occurrence_radial_used G g dg.toFullData 5','radial_left_used G g dg.occurrences 5 (gs 5 (by decide))')
prefix='''import Kobon.UpperOpenMathAntipodalAdjacency
import Kobon.UpperOpenMathTripleCharts

/-! Full unmarked two-cap triples cannot touch normalized balanced two-cap
triples. The opposite continuation need only be an actual used side, and
the neighbor's missing triangular sector is never assumed present. -/
namespace Kobon.UpperOpenMathAntipodalBalancedAdjacency
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalStarDegree UpperOpenMathSectorRecords
  UpperOpenMathAntipodalAdjacency UpperOpenMathTripleCharts Finset
set_option maxHeartbeats 1000000

theorem cap_left_at {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) (f.point z)=0 := by
  simpa only [f.triangle_support z hz,f.triangle_left z hz] using (f.triangle z).Aq

theorem cap_right_at {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) (f.point (z+1))=0 := by
  simpa only [f.triangle_support z hz,f.triangle_right z hz] using (f.triangle z).Ar

theorem cap_avoids_at {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) f.center≠0 := by
  simpa only [f.triangle_support z hz,f.triangle_center z hz] using (f.triangle z).Ap

theorem cap_eq_selected {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hp : z-1∈f.triangular) (hz : z∈f.triangular)
    (ho : OrdinaryAt n L (f.point z)) : f.opposite (z-1)=f.opposite z := by
  apply ordinary_nonradial_unique n L (f.point z) ho (f.radial z)
    (f.opposite (z-1)) (f.opposite z) (f.radial_point z)
  · simpa only [sub_add_cancel] using cap_right_at f (z-1) hp
  · exact cap_left_at f z hz
  · intro h
    exact cap_avoids_at f (z-1) hp (by rw [h]; exact f.radial_center z)
  · intro h
    exact cap_avoids_at f z hz (by rw [h]; exact f.radial_center z)

theorem normalized_selected {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (g : Sectors n 3 L) (dg : NormalizedData G g)
    (z : ZMod 6) (hz : z∈({0,1,2,3,5} : Finset (ZMod 6))) : z∈g.triangular := by
  classical
  have ho0 := (g.mem_ordinaryShared 0).mp (by rw [dg.ordinary_eq]; simp)
  have ho3 := (g.mem_ordinaryShared 3).mp (by rw [dg.ordinary_eq]; simp)
  have hc1 : (1 : ZMod 6)∈g.coreShared := by rw [dg.core_eq]; simp
  have ht1 := (mem_filter.mp (mem_sdiff.mp hc1).1).1
  simp only [mem_insert,mem_singleton] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl
  · exact ho0.1
  · exact ht1
  · simpa using ho3.2.1
  · exact ho3.1
  · simpa using ho0.2.1

theorem radial_left_used {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (g : Sectors n 3 L)
    (occ : ∀ z∈g.triangular, Nonempty (Occurrence G g.center g.point z))
    (z : ZMod 6) (hz : z∈g.triangular) : {g.center,g.point z}∈usedEdges G := by
  obtain ⟨o⟩ := occ z hz
  have h := transported_side_used G o.index o.triangle o.transport 0
  change ({o.triangle.p,o.triangle.q} : Edge)∈usedEdges G at h
  rw [o.center,o.left] at h
  exact h

theorem radial_right_used {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (g : Sectors n 3 L)
    (occ : ∀ z∈g.triangular, Nonempty (Occurrence G g.center g.point z))
    (z : ZMod 6) (hz : z∈g.triangular) : {g.center,g.point (z+1)}∈usedEdges G := by
  obtain ⟨o⟩ := occ z hz
  have h := transported_side_used G o.index o.triangle o.transport 2
  change ({o.triangle.r,o.triangle.p} : Edge)∈usedEdges G at h
  rw [o.center,o.right] at h
  simpa only [pair_comm] using h

'''
target=ROOT/'work/seed_search/antipodal-balanced-base.lean'
target.parent.mkdir(parents=True,exist_ok=True)
target.write_text(prefix+body+'\n#print axioms normalized_right_pair_incompatible\nend Kobon.UpperOpenMathAntipodalBalancedAdjacency\n',encoding='utf-8')
print('Generated partial-neighbor base',len((prefix+body).splitlines()),'lines')
