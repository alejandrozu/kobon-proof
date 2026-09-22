import Kobon.BBLCaps

/-! Finite assembly of a BBL doubling witness.
The source labels put Y0 first; the target labels put Y0 last. Replaced
old triangles have two old supports, whereas mixed triangles have two
auxiliary supports. This makes their lists disjoint. -/
namespace Kobon.BBLAssembly
open BBLRowGeometry BBLCaps

def replace (r : Nat) (t : Triple) : Triple :=
  if t.i=0 then ⟨t.j-1,t.k-1,4*r+capRow r (t.j-1)⟩
  else ⟨t.i-1,t.j-1,t.k-1⟩

theorem replace_second_lt (r : Nat) (t : Triple)
    (hij : t.i < t.j) (hjk : t.j < t.k) (hkn : t.k < 4*r+1) :
    (replace r t).j < 4*r := by
  unfold replace
  split_ifs <;> dsimp <;> omega

theorem replace_injective_on (r : Nat) (t u : Triple)
    (hti : t.i < t.j) (htj : t.j < t.k) (htk : t.k < 4*r+1)
    (hui : u.i < u.j) (huj : u.j < u.k) (huk : u.k < 4*r+1)
    (he : replace r t=replace r u) : t=u := by
  have h1 := congrArg Triple.i he
  have h2 := congrArg Triple.j he
  have h3 := congrArg Triple.k he
  unfold replace at h1 h2 h3
  split_ifs at h1 h2 h3 <;> dsimp at h1 h2 h3
  all_goals
    cases t
    cases u
    simp only [Triple.mk.injEq]
    dsimp at *
    omega

theorem replaced_witness (r : Nat) (old new : Nat → Line ℝ)
    (ts : List Triple) (hn : ts.Nodup)
    (hold : ∀ t ∈ ts, TrianglePredicate (4*r+1) old t)
    (hnew : ∀ t ∈ ts, TrianglePredicate (8*r+1) new (replace r t)) :
    (ts.map (replace r)).Nodup ∧
      (∀ t ∈ ts.map (replace r), TrianglePredicate (8*r+1) new t ∧ t.j < 4*r) ∧
      (ts.map (replace r)).length=ts.length := by
  refine ⟨List.Nodup.map_on ?_ hn,?_,by simp⟩
  · intro t ht u hu he
    obtain ⟨hi,hj,hk,_⟩ := hold t ht
    obtain ⟨hii,hjj,hkk,_⟩ := hold u hu
    exact replace_injective_on r t u hi hj hk hii hjj hkk he
  · intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    obtain ⟨hi,hj,hk,_⟩ := hold u hu
    exact ⟨hnew u hu,replace_second_lt r u hi hj hk⟩

/-- Once the analytic construction supplies all replaced old cells and the
crossing order, the full q² gain follows without any overlap assumption. -/
theorem doubling_bound (r T : Nat) (hr : 1 ≤ r) (old new : Nat → Line ℝ)
    (w : Line ℝ) (ts : List Triple) (hn : ts.Nodup)
    (hold : ∀ t ∈ ts, TrianglePredicate (4*r+1) old t) (hcount : T ≤ ts.length)
    (hp : NoParallel (8*r+1) new) (hs : NoConcurrent (8*r+1) new)
    (hw : Exterior.Admissible (8*r+1) new w) (horder : CrossingOrder r new w)
    (hnew : ∀ t ∈ ts, TrianglePredicate (8*r+1) new (replace r t)) :
    SimpleLowerBound (8*r+1) (T+(4*r)^2) := by
  obtain ⟨hrn,hrt,hrc⟩ := replaced_witness r old new ts hn hold hnew
  obtain ⟨ms,hmn,hmt,hmc⟩ := mixed_witness r hr new w hp hs hw horder
  let rs := ts.map (replace r)
  have hdisjoint : rs.Disjoint ms := by
    intro t ht hm
    have hlt := (hrt t ht).2
    have hge := (hmt t hm).2
    omega
  refine ⟨new,hp,hs,rs++ms,hrn.append hmn hdisjoint,?_,?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hrt t ht).1
    · exact (hmt t ht).1
  · dsimp [rs]
    rw [List.length_append,List.length_map]
    omega

#print axioms replace_injective_on
#print axioms doubling_bound
end Kobon.BBLAssembly
