import Kobon.BBLCapBridge
import Kobon.BBLCentralPersistence
import Kobon.BBLConsecutive
import Kobon.BBLAssembly

/-! Retention of every old Y0 triangle, including the central gap. -/
namespace Kobon.BBLCapRetention
open Filter BBLExtrema BBLPersistence BBLCaps BBLAssembly BBLCapBridge
  BBLCentralPersistence BBLConsecutive
open scoped Topology

theorem cap_retained_eventually (r : Nat) (hr : 1 ≤ r) (old D : Nat → Line ℝ)
    (m a : Nat → ℝ) (hp : NoParallel (4*r+1) old) (hs : NoConcurrent (4*r+1) old)
    (hzero : old 0=graphLine 0 0)
    (hgraph : ∀ j < 4*r, old (j+1)=graphLine (m j) (a j))
    (hordered : ∀ i j, i < j → j < 4*r → a i < a j)
    (hcap : ∀ j, j < 4*r-1 → j ≠ 2*r-1 → ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ →
      CanonicalEndpointSigns r j
        (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)))
    (hcentral : ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ → CanonicalCentralSigns r
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)))
    (t : Triple) (ht : TrianglePredicate (4*r+1) old t) (hti : t.i=0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ → TrianglePredicate (8*r+1)
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) (replace r t) := by
  rcases t with ⟨i,j,k⟩
  change i=0 at hti
  subst i
  have hi : 0 < j := ht.1
  have hk : k < 4*r+1 := ht.2.2.1
  have hcon := supports_consecutive (4*r) j k old m a hp hzero hgraph hordered ht
  subst k
  by_cases hcen : j=2*r
  · subst j
    have hh := central_replaced_eventually r hr old D hp ht
    filter_upwards [hh,hcentral] with κ hκ hsign
    intro hpositive
    have htri := hκ (hsign hpositive)
    have hrow := capRow_central r hr
    simpa [replace,Nat.add_sub_cancel_right,hrow,
      show 4*r+4*r=8*r by omega] using htri
  · have hjgap : j-1 < 4*r-1 := by omega
    have hgap : j-1 ≠ 2*r-1 := by omega
    have hfirst : j-1+1=j := by omega
    have hsecond : j-1+2=j+1 := by omega
    have htgap : TrianglePredicate (4*r+1) old ⟨0,j-1+1,j-1+2⟩ := by
      simpa only [hfirst,hsecond] using ht
    have hh := cap_replaced_eventually r (j-1) hr hjgap hgap old D hp hs htgap
    filter_upwards [hh,hcap (j-1) hjgap hgap] with κ hκ hsign
    intro hpositive
    have htri := hκ (hsign hpositive)
    simpa [replace,Nat.add_sub_cancel_right,hfirst] using htri

#print axioms cap_retained_eventually
end Kobon.BBLCapRetention
