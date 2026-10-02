import Kobon.BBLSeed21
import Kobon.Permutation
import Kobon.BBLRealizedPencil
import Kobon.BBLRecursiveSeed

/-! Put the verified 21-line parameter seed into the recursively sorted grid.
This only permutes labels. The rational seed certificates retain their stated
native-evaluation trust; no new geometric hypothesis is introduced.
-/
namespace Kobon.BBLSeed21Normalized
open Real Parametric Exterior BBLExtrema BBLAnalytic BBLCrossingCoordinates
  BBLRealizedPencil BBLGridCuts Permutation
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def perm (i : Nat) : Nat :=
  (#[0,11,1,12,2,13,3,14,4,15,5,6,16,7,17,8,18,9,19,10,20] : Array Nat)[i]!

theorem perm_bound (i : Fin 21) : perm i<21 := by
  have h : ∀ j : Fin 21, perm j<21 := by decide +kernel
  exact h i

theorem perm_injective (i j : Fin 21) (h : perm i=perm j) : i=j := by
  have hi : ∀ a b : Fin 21, perm a=perm b → a=b := by decide +kernel
  exact hi i j h

noncomputable def slopes (j : Nat) : ℝ := (BBLSeed21.lineAt (perm (j+1))).a

theorem graph_identity (ε : ℝ) (i : Nat) (hi : i<21) :
    BBLSeed21.arrangement ε (perm i)=oldArrangement 5 ε slopes i := by
  have hi' : i≤20 := by omega
  interval_cases i <;>
    norm_num [BBLSeed21.arrangement,BBLSeed21.lineAt,BBLSeed21.lines,
      BBLSeed21.parameters,perm,slopes,oldArrangement,oldIntercept,cut,
      leftAngle,rightAngle,alpha,toLine,graphLine,evaluate,Fin.sum_univ_succ]
  all_goals congr 1
  all_goals ring_nf
  all_goals simp only [neg_div,mul_neg,Real.tan_neg]
  all_goals ring

theorem no_parallel (ε : ℝ) : NoParallel 21 (oldArrangement 5 ε slopes) := by
  apply Permutation.no_parallel_congr 21 (fun i => BBLSeed21.arrangement ε (perm i))
    (oldArrangement 5 ε slopes) (graph_identity ε)
  exact Reindex.no_parallel_pullback 21 21 (BBLSeed21.arrangement ε) perm perm_bound
    perm_injective (BBLSeed21.no_parallel ε)

theorem no_concurrent (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000) :
    NoConcurrent 21 (oldArrangement 5 ε slopes) := by
  apply Permutation.no_concurrent_congr 21 (fun i => BBLSeed21.arrangement ε (perm i))
    (oldArrangement 5 ε slopes) (graph_identity ε)
  exact Reindex.no_concurrent_pullback 21 21 (BBLSeed21.arrangement ε) perm perm_bound
    perm_injective (BBLSeed21.no_concurrent ε hε hu)

theorem saturated (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000)
    (j : Nat) (hj : j<19) :
    TrianglePredicate 21 (oldArrangement 5 ε slopes) ⟨0,j+1,j+2⟩ := by
  have hmem : ∀ a : Fin 19,
      sortTriple (perm 0) (perm (a.val+1)) (perm (a.val+2))∈BBLSeed21.distinguished := by
    decide +kernel
  have ht := BBLSeed21.all_distinguished ε hε hu _ (hmem ⟨j,hj⟩)
  apply Permutation.triangle_congr 21 (fun i => BBLSeed21.arrangement ε (perm i))
    (oldArrangement 5 ε slopes) (graph_identity ε)
  exact triangle_pullback_support 21 21 (BBLSeed21.arrangement ε) perm perm_bound
    (sortTriple (perm 0) (perm (j+1)) (perm (j+2))) ht
    0 (j+1) (j+2) (by omega) (by omega) (by omega)
    (fun x => (sortTriple_mem (perm 0) (perm (j+1)) (perm (j+2)) x).symm)

theorem central_height (ε : ℝ) :
    (intersection (oldArrangement 5 ε slopes 10) (oldArrangement 5 ε slopes 11)).2=5*ε/2 := by
  rw [← graph_identity ε 10 (by decide),← graph_identity ε 11 (by decide)]
  norm_num [BBLSeed21.arrangement,BBLSeed21.lineAt,BBLSeed21.lines,
    BBLSeed21.parameters,perm,toLine,evaluate,Fin.sum_univ_succ,intersection,vertex,det]
  ring

theorem seed_with_slopes (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000) :
    ∃ s : BBLRecursiveSeed.Seed 5 132 ε, s.slopes=slopes := by
  obtain ⟨ts,hn,ht,hc⟩ := transport_list_of_injective 21 (BBLSeed21.arrangement ε)
    perm perm_bound perm_injective BBLSeed21.triangles
    (increasing_nodup 21 _ BBLSeed21.ordered) (BBLSeed21.all_triangles ε hε hu)
  refine ⟨⟨slopes,ts,no_parallel ε,no_concurrent ε hε hu,?_,?_,hn,?_,?_⟩,rfl⟩
  · intro j hj
    exact saturated ε hε hu j hj
  · norm_num only at ⊢
    rw [central_height]
    positivity
  · intro t htm
    exact Permutation.triangle_congr 21 _ _ (graph_identity ε) t (ht t htm)
  · have hlen : BBLSeed21.triangles.length=132 := by decide +kernel
    omega

theorem compatible (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000) :
    BBLRecursiveSeed.Compatible 5 132 ε := by
  obtain ⟨s,_⟩ := seed_with_slopes ε hε hu
  exact ⟨s⟩

#print axioms graph_identity
#print axioms compatible

end Kobon.BBLSeed21Normalized
