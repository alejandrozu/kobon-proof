import Kobon.OpenMathConstructionSeed61Data
import Kobon.OpenMathConstructionLineEquality
namespace Kobon.OpenMathConstructionSeed61Fast
open Parametric OpenMathIntegerBoxes OpenMathConstructionRescale
open OpenMathConstructionLineEquality OpenMathConstructionSeed61
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem rescale_inverse {d : Nat} (s : ℚ) (hs : s≠0) (l : ParamLine d) :
    rescale s (rescale (1/s) l)=l := by
  apply paramLine_ext
  · dsimp [rescale]; field_simp
  · dsimp [rescale]; field_simp
  · funext i
    dsimp [rescale,scale]
    field_simp

theorem line_matching (i : Fin 61) :
    castLine (intLineAt i)=rescale (lineFactor i) (lineAt i) :=
  (rescale_inverse (lineFactor i) (ne_of_gt (lineFactor_pos i)) (castLine (intLineAt i))).symm

theorem gridLo_matching : grid gridDen loInt=lo := rfl
theorem gridHi_matching : grid gridDen hiInt=hi := rfl

theorem intSimple_transfer (h : SimpleCheck 61 (grid gridDen loInt) (grid gridDen hiInt)
    29 (fun i => castLine (intLineAt i))) : SimpleCheck 61 lo hi 29 lineAt := by
  apply simple_descaling 61 lo hi 29 lineAt lineFactor lineFactor_pos
  exact simpleCheck_congr 61 lo hi 29 (fun i => castLine (intLineAt i))
    (fun i => rescale (lineFactor i) (lineAt i)) line_matching h

theorem intTriangle_transfer (t : Triple)
    (h : TriangleCheck 61 (grid gridDen loInt) (grid gridDen hiInt)
      (fun i => castLine (intLineAt i)) t) : TriangleCheck 61 lo hi lineAt t := by
  apply triangle_descaling 61 lo hi lineAt lineFactor lineFactor_pos t
  exact triangleCheck_congr 61 lo hi (fun i => castLine (intLineAt i))
    (fun i => rescale (lineFactor i) (lineAt i)) line_matching t h

#print axioms line_matching
#print axioms intSimple_transfer
end Kobon.OpenMathConstructionSeed61Fast
