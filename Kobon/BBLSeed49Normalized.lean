import Kobon.BBLSeed49
import Kobon.Permutation
import Kobon.BBLRealizedPencil
import Kobon.BBLRecursiveSeed

/-! The sorted actual 49-line parameter seed satisfies the complete recursive
geometric invariant. Its finite box checks retain native-evaluation trust. -/
namespace Kobon.BBLSeed49Normalized
open Real Parametric Exterior BBLExtrema BBLAnalytic BBLCrossingCoordinates
  BBLRealizedPencil BBLGridCuts
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def slopes (j : Nat) : ℝ := (BBLSeed49.lineAt (j+1)).a

theorem graph_identity (ε : ℝ) (i : Nat) (hi : i<49) :
    BBLSeed49.arrangement ε i=oldArrangement 12 ε slopes i := by
  have hi' : i≤48 := by omega
  interval_cases i <;>
    norm_num [BBLSeed49.arrangement,BBLSeed49.lineAt,BBLSeed49.lines,
      BBLSeed49.parameters,slopes,oldArrangement,oldIntercept,cut,
      leftAngle,rightAngle,alpha,toLine,graphLine,evaluate,Fin.sum_univ_succ]
  all_goals congr 1
  all_goals ring_nf
  all_goals simp only [neg_div,mul_neg,Real.tan_neg]
  all_goals ring

theorem no_parallel (ε : ℝ) : NoParallel 49 (oldArrangement 12 ε slopes) :=
  Permutation.no_parallel_congr 49 _ _ (graph_identity ε) (BBLSeed49.no_parallel ε)

theorem no_concurrent (ε : ℝ) (he : 0<ε) (hu : ε≤1/100) :
    NoConcurrent 49 (oldArrangement 12 ε slopes) :=
  Permutation.no_concurrent_congr 49 _ _ (graph_identity ε)
    (BBLSeed49.no_concurrent ε he hu)

theorem saturated (ε : ℝ) (he : 0<ε) (hu : ε≤1/100)
    (j : Nat) (hj : j<47) :
    TrianglePredicate 49 (oldArrangement 12 ε slopes) ⟨0,j+1,j+2⟩ := by
  have hmem : ∀ a : Fin 47, (⟨0,a.val+1,a.val+2⟩ : Triple)∈BBLSeed49.distinguished := by
    decide +kernel
  exact Permutation.triangle_congr 49 _ _ (graph_identity ε) _
    (BBLSeed49.all_distinguished ε he hu _ (hmem ⟨j,hj⟩))

theorem central_height (ε : ℝ) :
    (intersection (oldArrangement 12 ε slopes 24)
      (oldArrangement 12 ε slopes 25)).2=(5000000000/212664377:ℝ)*ε := by
  rw [← graph_identity ε 24 (by decide),← graph_identity ε 25 (by decide)]
  norm_num [BBLSeed49.arrangement,BBLSeed49.lineAt,BBLSeed49.lines,
    BBLSeed49.parameters,toLine,evaluate,Fin.sum_univ_succ,intersection,vertex,det]
  ring

theorem seed_with_slopes (ε : ℝ) (he : 0<ε) (hu : ε≤1/100) :
    ∃ s : BBLRecursiveSeed.Seed 12 767 ε, s.slopes=slopes := by
  refine ⟨⟨slopes,BBLSeed49.triangles,no_parallel ε,no_concurrent ε he hu,
    ?_,?_,increasing_nodup 49 _ BBLSeed49.ordered,?_,?_⟩,rfl⟩
  · intro j hj
    exact saturated ε he hu j hj
  · norm_num only at ⊢
    rw [central_height]
    positivity
  · intro t ht
    exact Permutation.triangle_congr 49 _ _ (graph_identity ε) t
      (BBLSeed49.all_triangles ε he hu t ht)
  · decide +kernel

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤1/100) :
    BBLRecursiveSeed.Compatible 12 767 ε := by
  obtain ⟨s,_⟩ := seed_with_slopes ε he hu
  exact ⟨s⟩

#print axioms graph_identity
#print axioms central_height
#print axioms compatible
end Kobon.BBLSeed49Normalized
