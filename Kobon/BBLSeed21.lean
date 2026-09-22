import Kobon.HybridBoundary
import Kobon.BBLExtrema
import Kobon.BBLTangentBounds
import Mathlib.Tactic.FinCases

/-! A complete real-parameter 21-line seed certificate.
The rational slopes are fixed. The intercepts are actual tan(k*pi/20).
The finite box checks use native_decide; geometry and trigonometric bounds are
proved by the generic soundness theorems. This does not formalize BBL doubling.
-/
namespace Kobon.BBLSeed21
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lo : Form 10 := ![(79192220162268146919441546347/500000000000000000000000000000),(3249196962329063261558714122151344649549/10000000000000000000000000000000000000000),(407620359595543048410965529/800000000000000000000000000),(45408908000335055368466672342538671851/62500000000000000000000000000000000000),1,(137638192047117353820720958191088767/100000000000000000000000000000000000),(4906526263762876455761601/2500000000000000000000000),(153884176858762670128514528801845491/50000000000000000000000000000000000),(31568757573375215494897321/5000000000000000000000000),0]
def hi : Form 10 := ![(31676888064907258767776618539/200000000000000000000000000000),(64983939246581265231174282443026892991/200000000000000000000000000000000000000),(509525449494428810513706911251/1000000000000000000000000000000),(7265425280053608858954667574806187496161/10000000000000000000000000000000000000000),1,(1075298375368104326724382485867881/781250000000000000000000000000000),(3925221011010301164609281/2000000000000000000000000),(307768353717525340257029057603690983/100000000000000000000000000000000000),(63137515146750430989794643/10000000000000000000000000),(1/100000)]

def lines : Array (ParamLine 10) := #[
  ⟨0,-1,![0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(2/3),-1,![0,0,0,0,0,0,0,(-2/3),0,0]⟩,
  ⟨-5,-1,![0,0,0,0,0,5,0,0,0,0]⟩,
  ⟨(5/7),-1,![0,0,0,(-5/7),0,0,0,0,0,0]⟩,
  ⟨10,-1,![0,-10,0,0,0,0,0,0,0,0]⟩,
  ⟨(5/2),-1,![0,0,0,0,0,0,0,0,0,(-5/2)]⟩,
  ⟨(-5/2),-1,![0,0,0,0,0,0,0,0,0,(-5/2)]⟩,
  ⟨2,-1,![0,2,0,0,0,0,0,0,0,0]⟩,
  ⟨(-10/3),-1,![0,0,0,(-10/3),0,0,0,0,0,0]⟩,
  ⟨(5/6),-1,![0,0,0,0,0,(5/6),0,0,0,0]⟩,
  ⟨-2,-1,![0,0,0,0,0,0,0,-2,0,0]⟩,
  ⟨(-1030057175864625828795291/50000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,(1030057175864625828795291/50000000000000000000000000000000000),0]⟩,
  ⟨(-5393450026002646123540693/100000000000000000000000000000000000),-1,![0,0,0,0,0,0,(5393450026002646123540693/100000000000000000000000000000000000),0,0,0]⟩,
  ⟨(-3333336666666666666666667/50000000000000000000000000000000000),-1,![0,0,0,0,(3333336666666666666666667/50000000000000000000000000000000000),0,0,0,0,0]⟩,
  ⟨(-5393459713236352861685839/100000000000000000000000000000000000),-1,![0,0,(5393459713236352861685839/100000000000000000000000000000000000),0,0,0,0,0,0,0]⟩,
  ⟨(-41203107750194946552719/2000000000000000000000000000000000),-1,![(41203107750194946552719/2000000000000000000000000000000000),0,0,0,0,0,0,0,0,0]⟩,
  ⟨(2060155387509747327635949/100000000000000000000000000000000000),-1,![(2060155387509747327635949/100000000000000000000000000000000000),0,0,0,0,0,0,0,0,0]⟩,
  ⟨(2696729856618176430842919/50000000000000000000000000000000000),-1,![0,0,(2696729856618176430842919/50000000000000000000000000000000000),0,0,0,0,0,0,0]⟩,
  ⟨(6666673333333333333333333/100000000000000000000000000000000000),-1,![0,0,0,0,(6666673333333333333333333/100000000000000000000000000000000000),0,0,0,0,0]⟩,
  ⟨(1348362506500661530885173/25000000000000000000000000000000000),-1,![0,0,0,0,0,0,(1348362506500661530885173/25000000000000000000000000000000000),0,0,0]⟩,
  ⟨(2060114351729251657590581/100000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,(2060114351729251657590581/100000000000000000000000000000000000),0]⟩]

def lineAt (i : Nat) : ParamLine 10 := lines[i]!

def triangles : List Triple := [⟨0,1,11⟩,⟨0,1,12⟩,⟨0,2,12⟩,⟨0,2,13⟩,⟨0,3,13⟩,⟨0,3,14⟩,⟨0,4,14⟩,⟨0,4,15⟩,⟨0,5,6⟩,⟨0,5,15⟩,⟨0,6,16⟩,⟨0,7,16⟩,⟨0,7,17⟩,⟨0,8,17⟩,⟨0,8,18⟩,⟨0,9,18⟩,⟨0,9,19⟩,⟨0,10,19⟩,⟨0,10,20⟩,⟨1,2,6⟩,⟨1,2,14⟩,⟨1,3,9⟩,⟨1,4,6⟩,⟨1,4,8⟩,⟨1,5,8⟩,⟨1,5,10⟩,⟨1,7,10⟩,⟨1,11,16⟩,⟨1,12,15⟩,⟨1,13,14⟩,⟨1,13,15⟩,⟨1,16,20⟩,⟨1,17,19⟩,⟨1,17,20⟩,⟨1,18,19⟩,⟨2,3,19⟩,⟨2,4,7⟩,⟨2,5,7⟩,⟨2,5,9⟩,⟨2,6,10⟩,⟨2,8,10⟩,⟨2,11,16⟩,⟨2,11,17⟩,⟨2,12,16⟩,⟨2,13,15⟩,⟨2,14,15⟩,⟨2,17,20⟩,⟨2,18,19⟩,⟨2,18,20⟩,⟨3,4,6⟩,⟨3,4,15⟩,⟨3,5,6⟩,⟨3,5,8⟩,⟨3,7,8⟩,⟨3,7,10⟩,⟨3,9,10⟩,⟨3,11,17⟩,⟨3,11,18⟩,⟨3,12,16⟩,⟨3,12,17⟩,⟨3,13,16⟩,⟨3,14,15⟩,⟨3,18,20⟩,⟨3,19,20⟩,⟨4,5,9⟩,⟨4,5,20⟩,⟨4,7,9⟩,⟨4,8,10⟩,⟨4,11,18⟩,⟨4,11,19⟩,⟨4,12,17⟩,⟨4,12,18⟩,⟨4,13,16⟩,⟨4,13,17⟩,⟨4,14,16⟩,⟨4,19,20⟩,⟨5,11,19⟩,⟨5,11,20⟩,⟨5,12,18⟩,⟨5,12,19⟩,⟨5,13,17⟩,⟨5,13,18⟩,⟨5,14,16⟩,⟨5,14,17⟩,⟨5,15,16⟩,⟨6,7,9⟩,⟨6,7,11⟩,⟨6,8,9⟩,⟨6,11,20⟩,⟨6,12,19⟩,⟨6,12,20⟩,⟨6,13,18⟩,⟨6,13,19⟩,⟨6,14,17⟩,⟨6,14,18⟩,⟨6,15,16⟩,⟨6,15,17⟩,⟨7,8,16⟩,⟨7,11,12⟩,⟨7,12,20⟩,⟨7,13,19⟩,⟨7,13,20⟩,⟨7,14,18⟩,⟨7,14,19⟩,⟨7,15,17⟩,⟨7,15,18⟩,⟨8,9,12⟩,⟨8,11,12⟩,⟨8,11,13⟩,⟨8,13,20⟩,⟨8,14,19⟩,⟨8,14,20⟩,⟨8,15,18⟩,⟨8,15,19⟩,⟨8,16,17⟩,⟨9,10,17⟩,⟨9,11,13⟩,⟨9,11,14⟩,⟨9,12,13⟩,⟨9,14,20⟩,⟨9,15,19⟩,⟨9,15,20⟩,⟨9,16,17⟩,⟨9,16,18⟩,⟨10,11,14⟩,⟨10,11,15⟩,⟨10,12,13⟩,⟨10,12,14⟩,⟨10,15,20⟩,⟨10,16,18⟩,⟨10,16,19⟩,⟨10,17,18⟩]

def distinguished : List Triple := [⟨0,1,11⟩,⟨0,1,12⟩,⟨0,2,12⟩,⟨0,2,13⟩,⟨0,3,13⟩,⟨0,3,14⟩,⟨0,4,14⟩,⟨0,4,15⟩,⟨0,5,6⟩,⟨0,5,15⟩,⟨0,6,16⟩,⟨0,7,16⟩,⟨0,7,17⟩,⟨0,8,17⟩,⟨0,8,18⟩,⟨0,9,18⟩,⟨0,9,19⟩,⟨0,10,19⟩,⟨0,10,20⟩]

def visible : List Triple := [⟨0,20,21⟩,⟨1,3,21⟩,⟨2,4,21⟩,⟨5,7,21⟩,⟨6,8,21⟩,⟨10,13,21⟩,⟨11,15,21⟩,⟨12,14,21⟩,⟨16,19,21⟩,⟨17,18,21⟩]

def rightSlope : ℚ := (2060114351729251657590581/100000000000000000000000000000000000)

theorem directions : DirectionCheck 21 lineAt := by native_decide
theorem simple : SimpleCheck 21 lo hi 9 lineAt := by native_decide
theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 21 lo hi lineAt t))=true := by native_decide
theorem distinguished_checks :
    distinguished.all (fun t => decide (TriangleCheck 21 lo hi lineAt t))=true := by native_decide
theorem ordered : Increasing 21 triangles := by decide +kernel
theorem admissible_check : AdmissibleCheck 21 lineAt 10 (-13) := by native_decide
theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 21 lo hi lineAt 10 (-13) t))=true := by native_decide

noncomputable def parameters (epsilon : ℝ) : Fin 10 → ℝ :=
  ![tan (1*π/20),tan (2*π/20),tan (3*π/20),tan (4*π/20),tan (5*π/20),
    tan (6*π/20),tan (7*π/20),tan (8*π/20),tan (9*π/20),epsilon]

noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · convert BBLTangentBounds.tan_1_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_2_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_3_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_4_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_5_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_6_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_7_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_8_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert BBLTangentBounds.tan_9_bounds using 1 <;> norm_num [lo,hi,parameters]
  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu

theorem no_parallel (epsilon : ℝ) : NoParallel 21 (arrangement epsilon) :=
  directions_sound 21 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    NoConcurrent 21 (arrangement epsilon) := by
  exact simple_sound 21 lo hi 9 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 21 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 21 lo hi 9 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈visible) :
    VisiblePair 21 (arrangement epsilon) (normalLine 10 (-13)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 21 lo hi lineAt 10 (-13) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈distinguished) : TrianglePredicate 21 (arrangement epsilon) t := by
  have hc := distinguished_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 21 lo hi 9 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem distinguished_count : distinguished.length=19 ∧ distinguished.Nodup := by decide +kernel
theorem visible_count : visible.length=10 ∧ visible.Nodup := by decide +kernel

theorem zero_line (epsilon : ℝ) : arrangement epsilon 0=graphLine 0 0 := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ]

theorem last_line (epsilon : ℝ) :
    arrangement epsilon 20=graphLine rightSlope (tan (9*π/20)) := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ,
    rightSlope,parameters]

theorem right_slope_positive : (0:ℝ)<rightSlope := by norm_num [rightSlope]
theorem right_slope_small : (rightSlope:ℝ)<10/13 := by norm_num [rightSlope]

theorem last_intersection (epsilon : ℝ) :
    intersection (arrangement epsilon 0) (arrangement epsilon 20)=(tan (9*π/20),0) := by
  rw [zero_line,last_line]
  have hm : (rightSlope:ℝ) ≠ 0 := ne_of_gt right_slope_positive
  simp [intersection,vertex,graphLine,det,hm]

theorem rightmost_last (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (r : Fin 21) (hr : r.val ≠ 20) :
    (intersection (arrangement epsilon 20) (arrangement epsilon r)).1≤tan (9*π/20) := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hp := no_parallel epsilon
  have hw : Admissible 21 L w := admissible_sound 21 lineAt 10 (-13) (parameters epsilon) admissible_check
  have hv : VisiblePair 21 L w ⟨0,20,21⟩ := all_visible epsilon he hu _ (by simp [visible])
  have hle := visible_extremal_right 21 L w hp hw ⟨0,20,21⟩ hv r hr
  have hdr : det (L 20) (L r) ≠ 0 := det_ne_of_ne 21 L hp ⟨20,by decide⟩ r (by
    intro hh
    exact hr (congrArg Fin.val hh).symm)
  have hdp : det (L 0) (L 20) ≠ 0 := hp ⟨0,by decide⟩ ⟨20,by decide⟩ (by decide)
  have hpr := intersection_on_left (L 20) (L r) hdr
  have hpp := intersection_on_right (L 0) (L 20) hdp
  have hlast : L 20=graphLine rightSlope (tan (9*π/20)) := last_line epsilon
  have hpr' : affineEval (graphLine rightSlope (tan (9*π/20))) (intersection (L 20) (L r))=0 := by
    rw [← hlast]
    exact hpr
  have hpp' : affineEval (graphLine rightSlope (tan (9*π/20))) (intersection (L 0) (L 20))=0 := by
    rw [← hlast]
    exact hpp
  have hdir : 0<w.a+w.b*(rightSlope:ℝ) := by
    dsimp [w,normalLine]
    norm_num [rightSlope]
  have hh := graph_projection_order rightSlope (tan (9*π/20)) w _ _ hpr' hpp' hdir hle
  simpa only [L,last_intersection,Prod.fst] using hh

theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 21 132 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,
    triangles,increasing_nodup 21 triangles ordered,all_triangles epsilon he hu,by decide⟩

theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 22 142 := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hw : Admissible 21 L w := admissible_sound 21 lineAt 10 (-13) (parameters epsilon) admissible_check
  have h := Exterior.extension 21 132 L triangles visible w (safeHeight 21 L w)
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 21 triangles ordered) (all_triangles epsilon he hu) (by decide)
    (by decide +kernel) (all_visible epsilon he hu) hw (safeHeight_beyond 21 L w)
  simpa [visible] using h

theorem arbitrarily_small (eta : ℝ) (heta : 0<eta) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<eta ∧ epsilon≤1/100000 ∧
      NoConcurrent 21 (arrangement epsilon) ∧
      (∀ t∈triangles, TrianglePredicate 21 (arrangement epsilon) t) ∧
      (∀ t∈visible, VisiblePair 21 (arrangement epsilon) (normalLine 10 (-13)) t) := by
  let epsilon := min (eta/2) (1/100000:ℝ)
  have he : 0<epsilon := lt_min (by linarith) (by norm_num)
  have hu : epsilon≤1/100000 := min_le_right _ _
  have hl : epsilon<eta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨epsilon,he,hl,hu,no_concurrent epsilon he hu,all_triangles epsilon he hu,all_visible epsilon he hu⟩

#print axioms simple_lower_bound
#print axioms exterior_lower_bound
#print axioms arbitrarily_small
#print axioms rightmost_last
end Kobon.BBLSeed21
