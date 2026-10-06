import Kobon.OpenMathConstructionSeed61
import Kobon.BBLRecursiveSeed
namespace Kobon.OpenMathConstructionSeed61Normalized
open Real Parametric Exterior BBLExtrema BBLAnalytic BBLCrossingCoordinates
  BBLRealizedPencil BBLGridCuts
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def slopes (j : Nat) : ℝ := (OpenMathConstructionSeed61.lineAt (j+1)).a

theorem graph_identity (ε : ℝ) (i : Nat) (hi : i<61) :
    OpenMathConstructionSeed61.arrangement ε i=oldArrangement 15 ε slopes i := by
  have hi' : i≤60 := by omega
  interval_cases i <;>
    norm_num [OpenMathConstructionSeed61.arrangement,OpenMathConstructionSeed61.lineAt,
      OpenMathConstructionSeed61.lines,OpenMathConstructionSeed61Fast.lineFactor,OpenMathConstructionSeed61Fast.intLineAt,OpenMathConstructionSeed61Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,OpenMathConstructionSeed61.parameters,slopes,
      oldArrangement,oldIntercept,cut,leftAngle,rightAngle,alpha,toLine,graphLine,
      evaluate,Fin.sum_univ_succ]
  all_goals congr 1
  all_goals ring_nf
  all_goals simp only [neg_div,mul_neg,Real.tan_neg]
  all_goals ring

theorem no_parallel (ε : ℝ) : NoParallel 61 (oldArrangement 15 ε slopes) :=
  BBLRecursiveSeed.no_parallel_congr 61 _ _ (graph_identity ε)
    (OpenMathConstructionSeed61.no_parallel ε)

theorem no_concurrent (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) :
    NoConcurrent 61 (oldArrangement 15 ε slopes) :=
  BBLRecursiveSeed.no_concurrent_congr 61 _ _ (graph_identity ε)
    (OpenMathConstructionSeed61.no_concurrent ε he hu)

theorem saturated (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) (j : Nat) (hj : j<59) :
    TrianglePredicate 61 (oldArrangement 15 ε slopes) ⟨0,j+1,j+2⟩ := by
  have hm : (⟨0,j+1,j+2⟩ : Triple)∈OpenMathConstructionSeed61.distinguished := by
    exact List.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩
  exact BBLRecursiveSeed.triangle_congr 61 _ _ (graph_identity ε) _
    (OpenMathConstructionSeed61.all_distinguished ε he hu _ hm)

theorem central_height (ε : ℝ) :
    (intersection (oldArrangement 15 ε slopes 30) (oldArrangement 15 ε slopes 31)).2=(20000000000/9239253)*ε := by
  rw [← graph_identity ε 30 (by decide),← graph_identity ε 31 (by decide)]
  norm_num [OpenMathConstructionSeed61.arrangement,OpenMathConstructionSeed61.lineAt,
    OpenMathConstructionSeed61.lines,OpenMathConstructionSeed61Fast.lineFactor,OpenMathConstructionSeed61Fast.intLineAt,OpenMathConstructionSeed61Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,OpenMathConstructionSeed61.parameters,
    toLine,evaluate,Fin.sum_univ_succ,intersection,vertex,det]
  ring

theorem seed_with_slopes (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) :
    ∃ s : BBLRecursiveSeed.Seed 15 1190 ε, s.slopes=slopes := by
  refine ⟨⟨slopes,OpenMathConstructionSeed61.triangles,no_parallel ε,no_concurrent ε he hu,
    saturated ε he hu,?_,increasing_nodup 61 _ OpenMathConstructionSeed61.ordered,?_,?_⟩,rfl⟩
  · norm_num only at ⊢
    rw [central_height]
    positivity
  · intro t ht
    exact BBLRecursiveSeed.triangle_congr 61 _ _ (graph_identity ε) _
      (OpenMathConstructionSeed61.all_triangles ε he hu _ ht)
  · decide +kernel

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) : BBLRecursiveSeed.Compatible 15 1190 ε := by
  obtain ⟨s,_⟩ := seed_with_slopes ε he hu
  exact ⟨s⟩

#print axioms graph_identity
#print axioms compatible
end Kobon.OpenMathConstructionSeed61Normalized

