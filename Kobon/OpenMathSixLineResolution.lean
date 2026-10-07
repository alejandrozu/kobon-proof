import Kobon.Cells
import Kobon.Simple
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-! Exact interval witnesses for an isolated triple resolution. The three old
central triangles occupy alternating radial sectors. For every0<ε<1/100,
moving the horizontal line up changes6 to7 triangles; moving it down changes
6 to4. Thus a reverse codimension-one collapse can gain2. These are concrete
geometry theorems, not an assumed general desingularization calculus. -/
namespace Kobon.OpenMathSixLineResolution
open Cells

def arrangement (ε : ℝ) : ℕ → Line ℝ
  | 0 => ⟨0,1,ε⟩
  | 1 => ⟨1,-1,0⟩
  | 2 => ⟨1,1,0⟩
  | 3 => ⟨1,2,3⟩
  | 4 => ⟨-2,1,2⟩
  | _ => ⟨1,4,-4⟩

def all6 : Finset Triple := {⟨0,1,2⟩,⟨0,1,3⟩,⟨0,1,4⟩,⟨0,1,5⟩,⟨0,2,3⟩,⟨0,2,4⟩,⟨0,2,5⟩,⟨0,3,4⟩,⟨0,3,5⟩,⟨0,4,5⟩,⟨1,2,3⟩,⟨1,2,4⟩,⟨1,2,5⟩,⟨1,3,4⟩,⟨1,3,5⟩,⟨1,4,5⟩,⟨2,3,4⟩,⟨2,3,5⟩,⟨2,4,5⟩,⟨3,4,5⟩}
noncomputable def triangles (L : ℕ → Line ℝ) : Finset Triple := by
  classical
  exact all6.filter (TrianglePredicate 6 L)

theorem ordered_member (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<6) :
    t∈all6 := by
  rcases t with ⟨i,j,k⟩
  simp only [all6,Finset.mem_insert,Finset.mem_singleton,Triple.mk.injEq]
  dsimp at hi hj hk
  have h1 : i≤3 := by omega
  have h2 : j≤4 := by omega
  have h3 : k≤5 := by omega
  interval_cases i <;> interval_cases j <;> interval_cases k <;> simp_all

def oldTriangles : Finset Triple := {⟨0,1,3⟩,⟨0,2,4⟩,⟨0,4,5⟩,⟨1,2,5⟩,⟨1,4,5⟩,⟨2,3,4⟩}

theorem old_triangle_iff (t : Triple) :
    TrianglePredicate 6 (arrangement (0)) t ↔ t∈oldTriangles := by
  constructor
  · intro ht
    have hm := ordered_member t ht.1 ht.2.1 ht.2.2.1
    simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · have hd := ht.2.2.2.1
      norm_num [arrangement,evalVertex,vertex,det] at hd
    · simp [oldTriangles]
    · have hh := ht.2.2.2.2 ⟨5,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨4,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [oldTriangles]
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [oldTriangles]
    · have hh := ht.2.2.2.2 ⟨4,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [oldTriangles]
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [oldTriangles]
    · simp [oldTriangles]
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
  · intro hm
    simp only [oldTriangles,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith

def upTriangles : Finset Triple := {⟨0,1,2⟩,⟨0,1,3⟩,⟨0,2,4⟩,⟨0,4,5⟩,⟨1,2,5⟩,⟨1,4,5⟩,⟨2,3,4⟩}

theorem up_triangle_iff (ε : ℝ) (he : 0<ε) (hs : ε<1/100) (t : Triple) :
    TrianglePredicate 6 (arrangement (ε)) t ↔ t∈upTriangles := by
  constructor
  · intro ht
    have hm := ordered_member t ht.1 ht.2.1 ht.2.2.1
    simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp [upTriangles]
    · simp [upTriangles]
    · have hh := ht.2.2.2.2 ⟨2,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨2,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [upTriangles]
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [upTriangles]
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [upTriangles]
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [upTriangles]
    · simp [upTriangles]
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
  · intro hm
    simp only [upTriangles,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith

def downTriangles : Finset Triple := {⟨0,1,2⟩,⟨0,4,5⟩,⟨1,4,5⟩,⟨2,3,4⟩}

theorem down_triangle_iff (ε : ℝ) (he : 0<ε) (hs : ε<1/100) (t : Triple) :
    TrianglePredicate 6 (arrangement (-ε)) t ↔ t∈downTriangles := by
  constructor
  · intro ht
    have hm := ordered_member t ht.1 ht.2.1 ht.2.2.1
    simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simp [downTriangles]
    · have hh := ht.2.2.2.2 ⟨2,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨5,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨4,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨1,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [downTriangles]
    · have hh := ht.2.2.2.2 ⟨4,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · simp [downTriangles]
    · simp [downTriangles]
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]
      all_goals linarith
  · intro hm
    simp only [downTriangles,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl|rfl
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
    · refine ⟨by decide,by decide,by decide,?_,?_⟩
      · norm_num [arrangement,evalVertex,vertex,det]
        all_goals linarith
      · intro r; fin_cases r
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inr ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith
        · refine Or.inl ⟨?_,?_,?_⟩ <;>
            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith

theorem triangle_set_complete (L : ℕ → Line ℝ) (t : Triple) :
    t∈triangles L ↔ TrianglePredicate 6 L t := by
  classical
  simp only [triangles,Finset.mem_filter]
  exact ⟨fun h=>h.2,fun h=>⟨ordered_member t h.1 h.2.1 h.2.2.1,h⟩⟩

theorem old_set : triangles (arrangement (0))=oldTriangles := by
  classical
  ext t
  simp only [triangle_set_complete,old_triangle_iff]

theorem old_count : (triangles (arrangement (0))).card=6 := by
  rw [old_set]
  decide

theorem up_set (ε : ℝ) (he : 0<ε) (hs : ε<1/100) : triangles (arrangement (ε))=upTriangles := by
  classical
  ext t
  simp only [triangle_set_complete,up_triangle_iff ε he hs]

theorem up_count (ε : ℝ) (he : 0<ε) (hs : ε<1/100) : (triangles (arrangement (ε))).card=7 := by
  rw [up_set ε he hs]
  decide

theorem down_set (ε : ℝ) (he : 0<ε) (hs : ε<1/100) : triangles (arrangement (-ε))=downTriangles := by
  classical
  ext t
  simp only [triangle_set_complete,down_triangle_iff ε he hs]

theorem down_count (ε : ℝ) (he : 0<ε) (hs : ε<1/100) : (triangles (arrangement (-ε))).card=4 := by
  rw [down_set ε he hs]
  decide

theorem reversal_gain_two (ε : ℝ) (he : 0<ε) (hs : ε<1/100) :
    (triangles (arrangement 0)).card=(triangles (arrangement (-ε))).card+2 := by
  rw [old_count,down_count ε he hs]

def broken : Finset Triple := {⟨0,1,3⟩,⟨0,2,4⟩,⟨1,2,5⟩}

theorem upward_keeps_all : upTriangles=oldTriangles∪{⟨0,1,2⟩} := by
  decide

theorem downward_breaks_three : downTriangles=(oldTriangles.filter fun t => t∉broken)∪{⟨0,1,2⟩} := by
  decide

theorem broken_card : broken.card=3 := by decide

noncomputable def interior (t : Triple) : Set Point :=
  OpenTriangle (intersection (arrangement 0 t.i) (arrangement 0 t.j))
    (intersection (arrangement 0 t.i) (arrangement 0 t.k))
    (intersection (arrangement 0 t.j) (arrangement 0 t.k))

theorem sector_zero (p : Point) (hp : p∈interior ⟨0,1,3⟩) :
    0<p.2 ∧ 0<p.1-p.2 := by
  rcases hp with ⟨u,v,w,hu,hv,hw,hs,rfl⟩
  norm_num [arrangement,intersection,vertex,det,barycenter]
  constructor <;> nlinarith
theorem sector_two (p : Point) (hp : p∈interior ⟨0,2,4⟩) :
    0<p.2 ∧ p.1+p.2<0 := by
  rcases hp with ⟨u,v,w,hu,hv,hw,hs,rfl⟩
  norm_num [arrangement,intersection,vertex,det,barycenter]
  constructor <;> nlinarith
theorem sector_four (p : Point) (hp : p∈interior ⟨1,2,5⟩) :
    p.2<0 ∧ 0<p.1-p.2 ∧ p.1+p.2<0 := by
  rcases hp with ⟨u,v,w,hu,hv,hw,hs,rfl⟩
  norm_num [arrangement,intersection,vertex,det,barycenter]
  refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem no_parallel (ε : ℝ) : NoParallel 6 (arrangement ε) := by
  intro i j hij
  change i.val<j.val at hij
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [arrangement,det]

theorem old_unique_triple (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<6) :
    evalVertex (arrangement 0 t.k) (arrangement 0 t.i) (arrangement 0 t.j)=0 ↔ t=⟨0,1,2⟩ := by
  have hm := ordered_member t hi hj hk
  simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals norm_num [arrangement,evalVertex,vertex,det,Triple.mk.injEq]

theorem up_nondegenerate (ε : ℝ) (he : 0<ε) (hs : ε<1/100)
    (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<6) :
    evalVertex (arrangement (ε) t.k) (arrangement (ε) t.i) (arrangement (ε) t.j)≠0 := by
  have hm := ordered_member t hi hj hk
  simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals norm_num [arrangement,evalVertex,vertex,det]
  all_goals linarith

theorem up_no_concurrent (ε : ℝ) (he : 0<ε) (hs : ε<1/100) :
    NoConcurrent 6 (arrangement (ε)) := by
  intro i j k hij hjk
  exact up_nondegenerate ε he hs ⟨i.val,j.val,k.val⟩ hij hjk k.isLt

theorem down_nondegenerate (ε : ℝ) (he : 0<ε) (hs : ε<1/100)
    (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<6) :
    evalVertex (arrangement (-ε) t.k) (arrangement (-ε) t.i) (arrangement (-ε) t.j)≠0 := by
  have hm := ordered_member t hi hj hk
  simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals norm_num [arrangement,evalVertex,vertex,det]
  all_goals linarith

theorem down_no_concurrent (ε : ℝ) (he : 0<ε) (hs : ε<1/100) :
    NoConcurrent 6 (arrangement (-ε)) := by
  intro i j k hij hjk
  exact down_nondegenerate ε he hs ⟨i.val,j.val,k.val⟩ hij hjk k.isLt

#print axioms no_parallel
#print axioms old_unique_triple
#print axioms up_no_concurrent
#print axioms down_no_concurrent

#print axioms up_triangle_iff
#print axioms down_triangle_iff
#print axioms reversal_gain_two
#print axioms downward_breaks_three
end Kobon.OpenMathSixLineResolution
