import Kobon.TamuraSeed33
import Kobon.Permutation
import Kobon.BBLRealizedPencil
import Kobon.BBLRecursiveSeed

/-! Put the verified 33-line parameter seed into the recursively sorted grid.
This only permutes labels. The rational seed certificates retain their stated
native-evaluation trust; no new geometric hypothesis is introduced.
-/
namespace Kobon.TamuraSeed33Normalized
open Real Parametric Exterior BBLExtrema BBLAnalytic BBLCrossingCoordinates
  BBLRealizedPencil BBLGridCuts Permutation
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def perm (i : Nat) : Nat :=
  (#[0,17,9,18,5,19,10,20,1,21,11,22,6,23,12,24,2,3,25,13,26,7,27,14,28,4,29,15,30,8,31,16,32] : Array Nat)[i]!

theorem perm_bound (i : Fin 33) : perm i<33 := by
  have h : ∀ j : Fin 33, perm j<33 := by decide +kernel
  exact h i

theorem perm_injective (i j : Fin 33) (h : perm i=perm j) : i=j := by
  have hi : ∀ a b : Fin 33, perm a=perm b → a=b := by decide +kernel
  exact hi i j h

noncomputable def slopes (j : Nat) : ℝ := (TamuraSeed33.lineAt (perm (j+1))).a

theorem graph_identity (ε : ℝ) (i : Nat) (hi : i<33) :
    TamuraSeed33.arrangement ε (perm i)=oldArrangement 8 ε slopes i := by
  have hi' : i≤32 := by omega
  interval_cases i <;>
    norm_num [TamuraSeed33.arrangement,TamuraSeed33.lineAt,TamuraSeed33.lines,
      TamuraSeed33.parameters,perm,slopes,oldArrangement,oldIntercept,cut,
      leftAngle,rightAngle,alpha,toLine,graphLine,evaluate,Fin.sum_univ_succ]
  all_goals congr 1
  all_goals ring_nf
  all_goals simp only [neg_div,mul_neg,Real.tan_neg]
  all_goals ring

theorem no_parallel (ε : ℝ) : NoParallel 33 (oldArrangement 8 ε slopes) := by
  apply Permutation.no_parallel_congr 33 (fun i => TamuraSeed33.arrangement ε (perm i))
    (oldArrangement 8 ε slopes) (graph_identity ε)
  exact Reindex.no_parallel_pullback 33 33 (TamuraSeed33.arrangement ε) perm perm_bound
    perm_injective (TamuraSeed33.no_parallel ε)

theorem no_concurrent (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000) :
    NoConcurrent 33 (oldArrangement 8 ε slopes) := by
  apply Permutation.no_concurrent_congr 33 (fun i => TamuraSeed33.arrangement ε (perm i))
    (oldArrangement 8 ε slopes) (graph_identity ε)
  exact Reindex.no_concurrent_pullback 33 33 (TamuraSeed33.arrangement ε) perm perm_bound
    perm_injective (TamuraSeed33.no_concurrent ε hε hu)

theorem saturated (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000)
    (j : Nat) (hj : j<31) :
    TrianglePredicate 33 (oldArrangement 8 ε slopes) ⟨0,j+1,j+2⟩ := by
  have hmem : ∀ a : Fin 31,
      sortTriple (perm 0) (perm (a.val+1)) (perm (a.val+2))∈TamuraSeed33.distinguished := by
    decide +kernel
  have ht := TamuraSeed33.all_distinguished ε hε hu _ (hmem ⟨j,hj⟩)
  apply Permutation.triangle_congr 33 (fun i => TamuraSeed33.arrangement ε (perm i))
    (oldArrangement 8 ε slopes) (graph_identity ε)
  exact triangle_pullback_support 33 33 (TamuraSeed33.arrangement ε) perm perm_bound
    (sortTriple (perm 0) (perm (j+1)) (perm (j+2))) ht
    0 (j+1) (j+2) (by omega) (by omega) (by omega)
    (fun x => (sortTriple_mem (perm 0) (perm (j+1)) (perm (j+2)) x).symm)

theorem central_height (ε : ℝ) :
    (intersection (oldArrangement 8 ε slopes 16) (oldArrangement 8 ε slopes 17)).2=ε/10 := by
  rw [← graph_identity ε 16 (by decide),← graph_identity ε 17 (by decide)]
  norm_num [TamuraSeed33.arrangement,TamuraSeed33.lineAt,TamuraSeed33.lines,
    TamuraSeed33.parameters,perm,toLine,evaluate,Fin.sum_univ_succ,intersection,vertex,det]
  ring

theorem seed_with_slopes (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000) :
    ∃ s : BBLRecursiveSeed.Seed 8 341 ε, s.slopes=slopes := by
  obtain ⟨ts,hn,ht,hc⟩ := transport_list_of_injective 33 (TamuraSeed33.arrangement ε)
    perm perm_bound perm_injective TamuraSeed33.triangles
    (increasing_nodup 33 _ TamuraSeed33.ordered) (TamuraSeed33.all_triangles ε hε hu)
  refine ⟨⟨slopes,ts,no_parallel ε,no_concurrent ε hε hu,?_,?_,hn,?_,?_⟩,rfl⟩
  · intro j hj
    exact saturated ε hε hu j hj
  · norm_num only at ⊢
    rw [central_height]
    positivity
  · intro t htm
    exact Permutation.triangle_congr 33 _ _ (graph_identity ε) t (ht t htm)
  · have hlen : TamuraSeed33.triangles.length=341 := by decide +kernel
    omega

theorem compatible (ε : ℝ) (hε : 0<ε) (hu : ε≤1/100000) :
    BBLRecursiveSeed.Compatible 8 341 ε := by
  obtain ⟨s,_⟩ := seed_with_slopes ε hε hu
  exact ⟨s⟩

#print axioms graph_identity
#print axioms compatible

end Kobon.TamuraSeed33Normalized
