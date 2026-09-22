import Kobon.Cells
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Six shared sides at one triple point

A triangle and its three medians give six empty triangular cells. All six
radial segments incident to the center are sides of two distinct cells.
This refutes only a literal local incidence bound of two shared sides at a
multiple point. It does not refute any global Kobon upper bound.
-/
namespace Kobon.SharedFan
open Kobon.Cells

def integerLines : Array (Line ℤ) :=
  #[⟨1,0,0⟩,⟨0,1,0⟩,⟨1,1,3⟩,⟨1,-1,0⟩,⟨2,1,3⟩,⟨1,2,3⟩]

def integerLine : ℕ → Line ℤ := linesAt integerLines
noncomputable def realLine (i : ℕ) : Line ℝ := liftLine (integerLine i)

def triangle : Fin 6 → Triple :=
  ![⟨1,3,4⟩,⟨1,4,5⟩,⟨2,3,5⟩,⟨2,3,4⟩,⟨0,4,5⟩,⟨0,3,5⟩]

theorem integer_nonparallel : NoParallel 6 integerLine := by decide +kernel
theorem integer_triangles : ∀ i : Fin 6, TrianglePredicate 6 integerLine (triangle i) :=
  by decide +kernel
theorem triangle_injective : Function.Injective triangle := by decide +kernel

theorem real_nonparallel : NoParallel 6 realLine := noParallel_lift _ _ integer_nonparallel
theorem real_triangles (i : Fin 6) : TrianglePredicate 6 realLine (triangle i) :=
  triangle_lift _ _ _ (integer_triangles i)

noncomputable def geometry (i : Fin 6) : TriangleGeometry :=
  ofPredicate 6 realLine (triangle i) real_nonparallel (real_triangles i)

def center : Point := (1,1)
noncomputable def endpoint : Fin 6 → Point :=
  ![(0,0),(3/2,0),(3,0),(3/2,3/2),(0,3),(0,3/2)]

def previous (i : Fin 6) : Fin 6 := ⟨(i.val+5)%6,Nat.mod_lt _ (by decide)⟩

/-- A side is the closed segment joining two distinct vertices. This predicate
specifies its endpoints without selecting an orientation of the segment. -/
def SideEndpoints (p q : Point) (t : TriangleGeometry) : Prop :=
  p≠q ∧ ((p=t.p ∧ q=t.q) ∨ (p=t.q ∧ q=t.p) ∨
    (p=t.p ∧ q=t.r) ∨ (p=t.r ∧ q=t.p) ∨
    (p=t.q ∧ q=t.r) ∨ (p=t.r ∧ q=t.q))

theorem six_shared_sides (i : Fin 6) :
    SideEndpoints center (endpoint i) (geometry i) ∧
    SideEndpoints center (endpoint i) (geometry (previous i)) := by
  fin_cases i <;>
    norm_num [SideEndpoints,geometry,ofPredicate,center,endpoint,previous,
      triangle,intersection,vertex,det,realLine,liftLine,integerLine,linesAt,integerLines]

theorem adjacent_triangles_distinct (i : Fin 6) : triangle i≠triangle (previous i) := by
  fin_cases i <;> decide +kernel

theorem center_is_triple (i : Fin 6) :
    affineEval (realLine i) center=0 ↔ 3≤i.val := by
  fin_cases i <;>
    norm_num [affineEval,realLine,liftLine,integerLine,linesAt,integerLines,center]

theorem interiors_uncut (i r : Fin 6) :
    ∀ x∈(geometry i).interior, affineEval (realLine r) x≠0 :=
  interior_uncut 6 realLine (triangle i) real_nonparallel (real_triangles i) r

theorem interiors_nonempty (i : Fin 6) : (geometry i).interior.Nonempty :=
  interior_nonempty _

theorem interiors_disjoint (i j : Fin 6) (h : i≠j) :
    Disjoint (geometry i).interior (geometry j).interior :=
  distinct_interiors_disjoint 6 realLine _ _ real_nonparallel
    (real_triangles i) (real_triangles j) (fun e => h (triangle_injective e))

/-- Explicit affine parametrization of a radial closed segment. -/
noncomputable def radialPoint (i : Fin 6) (t : ℝ) : Point :=
  ((1-t)*center.1+t*(endpoint i).1,(1-t)*center.2+t*(endpoint i).2)

def radialSegment (i : Fin 6) : Set Point :=
  {x | ∃ t : ℝ, 0≤t ∧ t≤1 ∧ x=radialPoint i t}

theorem endpoint_on_segment (i : Fin 6) : endpoint i∈radialSegment i := by
  refine ⟨1,by norm_num,by norm_num,?_⟩
  simp [radialPoint]

theorem center_on_segment (i : Fin 6) : center∈radialSegment i := by
  refine ⟨0,by norm_num,by norm_num,?_⟩
  simp [radialPoint]

theorem radial_nonzero (i : Fin 6) : center≠endpoint i := (six_shared_sides i).1.1

theorem endpoint_not_on_other (i j : Fin 6) (h : i≠j) :
    endpoint i∉radialSegment j := by
  rintro ⟨t,ht0,ht1,he⟩
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  fin_cases i <;> fin_cases j
  all_goals try { contradiction }
  all_goals norm_num [endpoint,radialPoint,center] at hx hy
  all_goals linarith

theorem radial_segments_injective : Function.Injective radialSegment := by
  intro i j he
  by_contra h
  exact endpoint_not_on_other i j h (he ▸ endpoint_on_segment i)

/-- Each open radial segment contains no crossing by a different supporting
line: every arrangement line either contains the entire segment or misses its
relative interior. Thus these are elementary arrangement segments. -/
theorem radial_elementary (i r : Fin 6) :
    (affineEval (realLine r) center=0 ∧ affineEval (realLine r) (endpoint i)=0) ∨
    (∀ t : ℝ, 0<t → t<1 → affineEval (realLine r) (radialPoint i t)≠0) := by
  fin_cases i <;> fin_cases r <;>
    norm_num [affineEval,realLine,liftLine,integerLine,linesAt,integerLines,
      center,endpoint,radialPoint] <;>
    intros <;> linarith

#print axioms six_shared_sides
#print axioms center_is_triple
#print axioms interiors_disjoint
#print axioms radial_segments_injective
#print axioms radial_elementary

end Kobon.SharedFan
