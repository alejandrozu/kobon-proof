import Kobon.BBLRecursiveSeed

/-! The extra, explicit boundary data needed for maximal even companions. -/
namespace Kobon.BBLVisibleSeed
open Exterior BBLExtrema BBLCrossingCoordinates BBLRealizedPencil BBLRecursiveSeed

structure VisibleSeed (r T V : Nat) (ε : ℝ) (w : Line ℝ) extends Seed r T ε where
  visible : List Triple
  visible_nodup : visible.Nodup
  visible_valid : ∀ t∈visible, VisiblePair (4*r+1) (oldArrangement r ε slopes) w t
  visible_count : V≤visible.length
  admissible : Admissible (4*r+1) (oldArrangement r ε slopes) w
  right_positive : 0<slopes (4*r-1)
  right_direction : 0<w.a+w.b*slopes (4*r-1)
  right_boundary : ∀ i : Fin (4*r+1), i.val≠4*r →
    (intersection (oldArrangement r ε slopes (4*r)) (oldArrangement r ε slopes i)).1
      ≤oldIntercept r ε (4*r-1)

def Compatible (r T V : Nat) (ε : ℝ) (w : Line ℝ) : Prop :=
  Nonempty (VisibleSeed r T V ε w)

theorem even_lower_bound (r T V : Nat) (ε : ℝ) (w : Line ℝ)
    (h : Compatible r T V ε w) : SimpleLowerBound (4*r+2) (T+V) := by
  obtain ⟨s⟩ := h
  have hh := Exterior.extension (4*r+1) T (oldArrangement r ε s.slopes)
    s.triangles s.visible w (safeHeight (4*r+1) (oldArrangement r ε s.slopes) w)
    s.no_parallel s.no_concurrent s.nodup s.valid s.count s.visible_nodup
    s.visible_valid s.admissible (safeHeight_beyond (4*r+1) (oldArrangement r ε s.slopes) w)
  have hh' := hh.mono (Nat.add_le_add_left s.visible_count T)
  simpa only [Nat.add_assoc] using hh'

end Kobon.BBLVisibleSeed
