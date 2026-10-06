"""Promote the archived classical 33 seed through generic Boolean reflection.
The output theorem statements retain the old checks and actual trigonometric data.
Only the finite decision procedure is changed; no premise or coordinate is weakened.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
old=(ROOT/'research/three-hour-2026-10-02/drafts/TamuraSeed33.lean').read_text(encoding='utf-8')
ns='Kobon.OpenMathConstructionSeed33'
checks='''import Kobon.OpenMathConstructionSeed33Simple
namespace Kobon.OpenMathConstructionSeed33
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem triangles_bool :
    OpenMathConstructionBoolean.trianglesBool 33 lo hi lineAt triangles=true := by native_decide

theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 33 lo hi lineAt t))=true :=
  OpenMathConstructionBoolean.triangles_sound 33 lo hi lineAt triangles triangles_bool

theorem distinguished_subset_bool :
    distinguished.all (fun t => decide (t∈triangles))=true := by native_decide

theorem distinguished_checks :
    distinguished.all (fun t => decide (TriangleCheck 33 lo hi lineAt t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  exact (List.all_eq_true.mp triangle_checks) t
    (of_decide_eq_true ((List.all_eq_true.mp distinguished_subset_bool) t ht))

theorem ordered : Increasing 33 triangles := by decide +kernel

theorem admissible_bool :
    OpenMathConstructionBoolean.admissibleBool 33 lineAt 10 (-13)=true := by native_decide

theorem admissible_check : AdmissibleCheck 33 lineAt 10 (-13) :=
  OpenMathConstructionBoolean.admissible_sound 33 lineAt 10 (-13) admissible_bool

theorem visible_bool :
    OpenMathConstructionBoolean.visiblesBool 33 lo hi lineAt 10 (-13) visible=true := by native_decide

theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 33 lo hi lineAt 10 (-13) t))=true :=
  OpenMathConstructionBoolean.visibles_sound 33 lo hi lineAt 10 (-13) visible visible_bool

#print axioms triangle_checks
#print axioms visible_checks
end Kobon.OpenMathConstructionSeed33
'''
(ROOT/'Kobon/OpenMathConstructionSeed33Checks.lean').write_text(checks,encoding='utf-8',newline='\n')
body=old[old.index('noncomputable def parameters'):].replace('Kobon.TamuraSeed33',ns)
head='''import Kobon.OpenMathConstructionSeed33Checks
/-! Actual uniform classical 33-line seed, checked through executable Boolean reflection.
The source coordinates are the existing Forge--Ramirez Alfonsin construction.
The actual tangent bounds and geometric bridges are ordinary kernel proofs;
finite Bool computations retain the explicitly audited native-evaluation trust. -/
namespace Kobon.OpenMathConstructionSeed33
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
(ROOT/'Kobon/OpenMathConstructionSeed33.lean').write_text(head+'\n'+body,encoding='utf-8',newline='\n')
for suffix in ['Normalized','Visible']:
    s=(ROOT/f'research/three-hour-2026-10-02/drafts/TamuraSeed33{suffix}.lean').read_text(encoding='utf-8')
    s=s.replace('TamuraSeed33','OpenMathConstructionSeed33')
    (ROOT/f'Kobon/OpenMathConstructionSeed33{suffix}.lean').write_text(s,encoding='utf-8',newline='\n')
print('Generated 33 finite-check, actual-parameter, sorted-grid and visibility modules. Compilation pending.')