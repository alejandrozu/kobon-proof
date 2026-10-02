"""Generate the uniform 49-seed's independently checked exterior interface."""
from pathlib import Path
import json,re
ROOT=Path(__file__).resolve().parents[1]

def main():
    data=json.loads((ROOT/'research/three-hour-2026-10-02/constructions/uniform-grid49/visibility.json').read_text())
    pairs=data['visible_pairs']
    assert data['normal']==[1,-2] and len(pairs)==24
    body='''import Kobon.BBLSeed49
import Kobon.BBLProjection

namespace Kobon.BBLSeed49Exterior
open Real Parametric Exterior HybridBoundary BBLExtrema BBLSeed49
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rightSlope : ℚ := 1/3
'''
    body+='def visible : List Triple := ['+','.join('⟨'+','.join(map(str,t))+'⟩' for t in pairs)+']\n\n'
    body+='''theorem admissible_check : AdmissibleCheck 49 lineAt 1 (-2) := by native_decide
theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 49 lo hi lineAt 1 (-2) t))=true := by native_decide
theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100)
    (t : Triple) (ht : t∈visible) :
    VisiblePair 49 (arrangement epsilon) (normalLine 1 (-2)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 49 lo hi lineAt 1 (-2) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem visible_count : visible.length=24 ∧ visible.Nodup := by decide +kernel

'''
    template=(ROOT/'Kobon/BBLSeed21.lean').read_text()
    block=template[template.index('theorem zero_line'):template.index('theorem simple_lower_bound')]
    numbers={'21':'49','20':'48','9':'23','10':'1','13':'2','100000':'100'}
    block=re.sub(r'\b(21|20|9|10|13|100000)\b',lambda m:numbers[m.group()],block)
    body+=block
    body+='''theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100) :
    SimpleLowerBound 50 791 := by
  have h := Exterior.extension 49 767 (arrangement epsilon) triangles visible
    (normalLine 1 (-2)) (safeHeight 49 (arrangement epsilon) (normalLine 1 (-2)))
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 49 triangles ordered) (all_triangles epsilon he hu) (by decide)
    visible_count.2 (all_visible epsilon he hu)
    (admissible_sound 49 lineAt 1 (-2) (parameters epsilon) admissible_check)
    (safeHeight_beyond 49 (arrangement epsilon) (normalLine 1 (-2)))
  simpa [visible] using h

#print axioms all_visible
#print axioms rightmost_last
#print axioms exterior_lower_bound
end Kobon.BBLSeed49Exterior
'''
    (ROOT/'research/three-hour-2026-10-02/drafts/BBLSeed49Exterior.lean').write_text(body,encoding='utf-8',newline='\n')
    print('Wrote draft BBLSeed49Exterior.lean; full Lean compilation has not completed.')
if __name__=='__main__':main()
