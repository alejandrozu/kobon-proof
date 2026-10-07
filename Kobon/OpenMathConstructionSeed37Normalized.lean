import Kobon.OpenMathConstructionSeed37
import Kobon.BBLRecursiveSeed
namespace Kobon.OpenMathConstructionSeed37Normalized
open Real Parametric Exterior BBLExtrema BBLAnalytic BBLCrossingCoordinates
  BBLRealizedPencil BBLGridCuts
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def slopes (j : Nat) : ℝ := (OpenMathConstructionSeed37.lineAt (j+1)).a

theorem graph_identity (ε : ℝ) (i : Nat) (hi : i<37) :
    OpenMathConstructionSeed37.arrangement ε i=oldArrangement 9 ε slopes i := by
  have hi' : i≤36 := by omega
  interval_cases i <;>
    norm_num [OpenMathConstructionSeed37.arrangement,OpenMathConstructionSeed37.lineAt,
      OpenMathConstructionSeed37.lines,OpenMathConstructionSeed37Fast.lineFactor,OpenMathConstructionSeed37Fast.intLineAt,OpenMathConstructionSeed37Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,OpenMathConstructionSeed37.parameters,slopes,
      oldArrangement,oldIntercept,cut,leftAngle,rightAngle,alpha,toLine,graphLine,
      evaluate,Fin.sum_univ_succ]
  all_goals congr 1
  all_goals ring_nf
  all_goals simp only [neg_div,mul_neg,Real.tan_neg]
  all_goals ring

theorem no_parallel (ε : ℝ) : NoParallel 37 (oldArrangement 9 ε slopes) :=
  BBLRecursiveSeed.no_parallel_congr 37 _ _ (graph_identity ε)
    (OpenMathConstructionSeed37.no_parallel ε)

theorem no_concurrent (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) :
    NoConcurrent 37 (oldArrangement 9 ε slopes) :=
  BBLRecursiveSeed.no_concurrent_congr 37 _ _ (graph_identity ε)
    (OpenMathConstructionSeed37.no_concurrent ε he hu)

theorem saturated (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) (j : Nat) (hj : j<35) :
    TrianglePredicate 37 (oldArrangement 9 ε slopes) ⟨0,j+1,j+2⟩ := by
  have hm : (⟨0,j+1,j+2⟩ : Triple)∈OpenMathConstructionSeed37.distinguished := by
    exact List.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩
  exact BBLRecursiveSeed.triangle_congr 37 _ _ (graph_identity ε) _
    (OpenMathConstructionSeed37.all_distinguished ε he hu _ hm)

theorem central_height (ε : ℝ) :
    (intersection (oldArrangement 9 ε slopes 18) (oldArrangement 9 ε slopes 19)).2=(10000000000/540518163)*ε := by
  rw [← graph_identity ε 18 (by decide),← graph_identity ε 19 (by decide)]
  norm_num [OpenMathConstructionSeed37.arrangement,OpenMathConstructionSeed37.lineAt,
    OpenMathConstructionSeed37.lines,OpenMathConstructionSeed37Fast.lineFactor,OpenMathConstructionSeed37Fast.intLineAt,OpenMathConstructionSeed37Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,OpenMathConstructionSeed37.parameters,
    toLine,evaluate,Fin.sum_univ_succ,intersection,vertex,det]
  ring

theorem seed_with_slopes (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) :
    ∃ s : BBLRecursiveSeed.Seed 9 431 ε, s.slopes=slopes := by
  refine ⟨⟨slopes,OpenMathConstructionSeed37.triangles,no_parallel ε,no_concurrent ε he hu,
    saturated ε he hu,?_,increasing_nodup 37 _ OpenMathConstructionSeed37.ordered,?_,?_⟩,rfl⟩
  · norm_num only at ⊢
    rw [central_height]
    positivity
  · intro t ht
    exact BBLRecursiveSeed.triangle_congr 37 _ _ (graph_identity ε) _
      (OpenMathConstructionSeed37.all_triangles ε he hu _ ht)
  · decide +kernel

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) : BBLRecursiveSeed.Compatible 9 431 ε := by
  obtain ⟨s,_⟩ := seed_with_slopes ε he hu
  exact ⟨s⟩

#print axioms graph_identity
#print axioms compatible
end Kobon.OpenMathConstructionSeed37Normalized

