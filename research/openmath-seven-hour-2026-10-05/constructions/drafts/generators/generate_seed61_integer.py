from pathlib import Path
import json
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[3]
r=json.loads((ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text())
s=list(map(F,r['slopes'])); labs=r['labels']; D=10**20
forms=[[0]*30]
for m,lab in zip(s[1:],labs[1:]):
    c=[0]*30;c[lab[0]]=m.numerator*lab[1];forms.append(c)
v=lambda x:'!['+','.join(map(str,x))+']'
q=[F(t).denominator for t in r['slopes']]
lo=[int(F(t)*D) for t in r['lo']];hi=[int(F(t)*D) for t in r['hi']]
assert all(F(z,D)==F(t) for z,t in zip(lo,r['lo']))
assert all(F(z,D)==F(t) for z,t in zip(hi,r['hi']))
out='''import Kobon.OpenMathConstructionSeed61Data
import Kobon.OpenMathConstructionRescale
import Kobon.OpenMathIntegerBoxes
namespace Kobon.OpenMathConstructionSeed61
open Parametric OpenMathIntegerBoxes OpenMathConstructionRescale OpenMathConstructionBoolean
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
'''
out+=f'\ndef gridDen : ℤ := {D}\ndef loInt : IntForm 30 := {v(lo)}\ndef hiInt : IntForm 30 := {v(hi)}\n'
out+='def intLines : Array (IntLine 30) := #[\n'+',\n'.join('  ⟨'+str(m.numerator)+','+str(-m.denominator)+','+v(c)+'⟩' for m,c in zip(s,forms))+']\n'
out+='def intLineAt (i : Nat) : IntLine 30 := intLines[i]!\n'
out+='def lineFactor (i : Nat) : ℚ := ((lineAt i).a.den : Nat)\n'
out+='''theorem lineFactor_pos (i : Nat) : 0<lineFactor i := by
  unfold lineFactor
  exact_mod_cast (lineAt i).a.den_pos

def matchingBool : Bool := allFin 61 fun i =>
  let m := castLine (intLineAt i)
  let l := rescale (lineFactor i) (lineAt i)
  decide (m.a=l.a) && decide (m.b=l.b) && allFin 30 (fun j => decide (m.c j=l.c j))

theorem matching_bool : matchingBool=true := by native_decide

theorem line_matching (i : Fin 61) :
    castLine (intLineAt i)=rescale (lineFactor i) (lineAt i) := by
  have h := (allFin_true 61 _).mp matching_bool i
  simp only [matchingBool,Bool.and_eq_true,decide_eq_true_eq] at h
  have hc : (castLine (intLineAt i)).c=(rescale (lineFactor i) (lineAt i)).c := by
    funext j
    exact of_decide_eq_true ((allFin_true 30 _).mp h.2 j)
  cases hm : castLine (intLineAt i)
  cases hl : rescale (lineFactor i) (lineAt i)
  simp_all

def gridMatchingBool : Bool := allFin 30 fun i =>
  decide (grid gridDen loInt i=lo i) && decide (grid gridDen hiInt i=hi i)

theorem gridMatching_bool : gridMatchingBool=true := by native_decide

theorem gridLo_matching : grid gridDen loInt=lo := by
  funext i
  have h := (allFin_true 30 _).mp gridMatching_bool i
  exact of_decide_eq_true (Bool.and_eq_true.mp h).1

theorem gridHi_matching : grid gridDen hiInt=hi := by
  funext i
  have h := (allFin_true 30 _).mp gridMatching_bool i
  exact of_decide_eq_true (Bool.and_eq_true.mp h).2

theorem intSimple_transfer (h : SimpleCheck 61 (grid gridDen loInt) (grid gridDen hiInt)
    29 (fun i => castLine (intLineAt i))) : SimpleCheck 61 lo hi 29 lineAt := by
  rw [gridLo_matching,gridHi_matching] at h
  apply simple_descaling 61 lo hi 29 lineAt lineFactor lineFactor_pos
  intro i j k hij hjk
  have hh := h i j k hij hjk
  rwa [line_matching i,line_matching j,line_matching k] at hh

theorem intTriangle_transfer (t : Triple)
    (h : TriangleCheck 61 (grid gridDen loInt) (grid gridDen hiInt)
      (fun i => castLine (intLineAt i)) t) : TriangleCheck 61 lo hi lineAt t := by
  rw [gridLo_matching,gridHi_matching] at h
  obtain ⟨hi,hj,hk,hr⟩ := h
  have hii : t.i<61 := by omega
  have hjj : t.j<61 := by omega
  apply triangle_descaling 61 lo hi lineAt lineFactor lineFactor_pos t
  refine ⟨hi,hj,hk,?_⟩
  intro r
  have hh := hr r
  rw [line_matching r,line_matching ⟨t.i,hii⟩,line_matching ⟨t.j,hjj⟩,
    line_matching ⟨t.k,hk⟩] at hh
  exact hh

#print axioms line_matching
#print axioms intSimple_transfer
end Kobon.OpenMathConstructionSeed61
'''
(ROOT/'Kobon/OpenMathConstructionSeed61IntegerData.lean').write_text(out,encoding='utf-8',newline='\n')
print('Wrote integer data and matching bridges')
