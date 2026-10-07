import Kobon.OpenMathTranslationGerms
import Kobon.Simple
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

/-!
The exact static translation germs determine a finite supporting-triple count,
an actual straight-line lower-bound certificate, and a birth/loss identity.
The formula allows every concurrence pattern; it does not replace lost
triangles by a half-plane sector count.
-/
namespace Kobon.OpenMathTranslationCounting
open OpenMathTranslationGerms

abbrev Indices (n : ℕ) := Fin n × (Fin n × Fin n)

def tripleOf {n : ℕ} (a : Indices n) : Triple := ⟨a.1,a.2.1,a.2.2⟩

theorem tripleOf_injective (n : ℕ) : Function.Injective (tripleOf (n:=n)) := by
  intro a b h
  have hi := congrArg Triple.i h
  have hj := congrArg Triple.j h
  have hk := congrArg Triple.k h
  exact Prod.ext (Fin.ext hi) (Prod.ext (Fin.ext hj) (Fin.ext hk))

noncomputable def selected (n : ℕ) (L : ℕ → Line ℝ) : Finset (Indices n) := by
  classical
  exact Finset.univ.filter fun a=>TrianglePredicate n L (tripleOf a)

noncomputable def germs (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) : Finset (Indices n) := by
  classical
  exact Finset.univ.filter fun a=>TriangleGerm n L p (tripleOf a)

noncomputable def count (n : ℕ) (L : ℕ → Line ℝ) : ℕ := (selected n L).card
noncomputable def germCount (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) : ℕ := (germs n L p).card

theorem selected_stable (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) :
    Small (fun ε=>selected n (translate L p ε)=germs n L p) := by
  classical
  rcases simultaneous_triangle_stability n L p with ⟨η,hη,h⟩
  refine ⟨η,hη,?_⟩
  intro ε he hs
  ext a
  simp only [selected,germs,Finset.mem_filter,Finset.mem_univ,true_and]
  exact h ε he hs a.1 a.2.1 a.2.2

theorem count_stable (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) :
    Small (fun ε=>count n (translate L p ε)=germCount n L p) :=
  (selected_stable n L p).mono (fun _ h=>congrArg Finset.card h)

/-- A static germ count supplies an actual real-line lower bound. -/
theorem lower_bound_of_germ_count (n T : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (hp : NoParallel n L) (hc : T≤germCount n L p) :
    Small (fun _=>LowerBound n T) := by
  classical
  rcases selected_stable n L p with ⟨η,hη,h⟩
  let S := germs n L p
  let ts := (S.image tripleOf).toList
  have hlen : ts.length=S.card := by
    dsimp [ts]
    rw [Finset.length_toList,Finset.card_image_of_injective S (tripleOf_injective n)]
  refine ⟨η,hη,?_⟩
  intro ε he hs
  refine ⟨translate L p ε,translate_no_parallel n L p ε hp,ts,
    Finset.nodup_toList _,?_,?_⟩
  · intro t ht
    rcases Finset.mem_image.mp (Finset.mem_toList.mp ht) with ⟨a,ha,rfl⟩
    have ha' : a∈selected n (translate L p ε) := by
      rw [h ε he hs]
      exact ha
    exact (Finset.mem_filter.mp ha').2
  · rw [hlen]
    exact hc

theorem classical_bound_of_germ_count (n T : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (hp : NoParallel n L) (hc : T≤germCount n L p) : LowerBound n T := by
  rcases lower_bound_of_germ_count n T L p hp hc with ⟨η,hη,h⟩
  exact h (η/2) (by linarith) (by linarith)

noncomputable def lost (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) : Finset (Indices n) := by
  classical
  exact selected n L \ germs n L p

noncomputable def born (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) : Finset (Indices n) := by
  classical
  exact germs n L p \ selected n L

theorem static_birth_loss_identity (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) :
    germCount n L p+(lost n L p).card=count n L+(born n L p).card := by
  classical
  have h1 := Finset.card_inter_add_card_sdiff (selected n L) (germs n L p)
  have h2 := Finset.card_inter_add_card_sdiff (germs n L p) (selected n L)
  rw [Finset.inter_comm] at h2
  dsimp [germCount,count,lost,born]
  omega

/-- Exact wall crossing, with births and losses certified from coefficients. -/
theorem translated_birth_loss_identity (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) :
    Small (fun ε=>count n (translate L p ε)+(lost n L p).card=
      count n L+(born n L p).card) := by
  apply (count_stable n L p).mono
  intro ε h
  rw [h]
  exact static_birth_loss_identity n L p

#print axioms count_stable
#print axioms classical_bound_of_germ_count
#print axioms translated_birth_loss_identity
end Kobon.OpenMathTranslationCounting
