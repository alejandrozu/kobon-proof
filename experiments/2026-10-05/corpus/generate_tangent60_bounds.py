"""Generate Lean enclosures for tan(k*pi/60), using proved smaller grids.

The generator is untrusted: its output is a conventional Lean proof based
on subtraction, half-angle, and inverse identities.  Rational computations
are checked by norm_num within that proof.
"""
from pathlib import Path
from fractions import Fraction as F
import importlib.util, json, re

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "research/openmath-seven-hour-2026-10-05/corpus/tangent60"
OUT.mkdir(parents=True, exist_ok=True)


def existing(path, name):
    text = path.read_text(encoding="utf8")
    statement = text.split("theorem " + name + " :", 1)[1].split(":= by", 1)[0]
    numbers = re.findall(r"\(?(\d+)(?::ℝ)?\)?/(\d+)", statement)
    assert len(numbers) == 2, (name, numbers)
    return tuple(F(int(a), int(b)) for a, b in numbers)


def rat(x):
    return f"(({x.numerator}:ℝ)/{x.denominator})"


def rounded(iv, digits=24):
    d = 10**digits
    return F(iv[0]*d//1, d), F(-((-iv[1]*d)//1), d)


def sub(a, b):
    return rounded(((a[0]-b[1])/(1+a[1]*b[1]), (a[1]-b[0])/(1+a[0]*b[0])))


header = """import Kobon.BBLTangent48Bounds

/-! Rational enclosures for the actual denominator-60 tangent grid.
Generated proof text is checked by Lean: no floating values or evaluation
oracle occurs in the theorem dependency. -/
namespace Kobon.BBLTangent60Bounds
open Real BBLTangentBounds
set_option maxHeartbeats 0

theorem not_pole {x : ℝ} (hl : -(π/2)<x) (hu : x<π/2) :
    ∀ k : ℤ, x≠(2*k+1)*π/2 := by
  have hc : cos x≠0 := ne_of_gt (cos_pos_of_mem_Ioo ⟨hl,hu⟩)
  intro k he
  exact hc (cos_eq_zero_iff.mpr ⟨k,he⟩)

theorem subtraction_bounds (A B Alo Ahi Blo Bhi L U : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hAl : Alo≤A) (hAu : A≤Ahi)
    (hBl : Blo≤B) (hBu : B≤Bhi) (hBlo : 0≤Blo) (hAhi : 0≤Ahi)
    (hL : 0≤L) (hU : 0≤U)
    (hl : L*(1+Ahi*Bhi)≤Alo-Bhi)
    (hu : Ahi-Blo≤U*(1+Alo*Blo)) :
    L≤(A-B)/(1+A*B) ∧ (A-B)/(1+A*B)≤U := by
  have hd : 0<1+A*B := by positivity
  have hlo : Alo*Blo≤A*B := mul_le_mul hAl hBl hBlo hA
  have hhi : A*B≤Ahi*Bhi := mul_le_mul hAu hBu hB hAhi
  constructor
  · apply (le_div_iff₀ hd).mpr
    calc
      L*(1+A*B)≤L*(1+Ahi*Bhi) := mul_le_mul_of_nonneg_left (by linarith) hL
      _≤Alo-Bhi := hl
      _≤A-B := sub_le_sub hAl hBu
  · apply (div_le_iff₀ hd).mpr
    calc
      A-B≤Ahi-Blo := sub_le_sub hAu hBl
      _≤U*(1+Alo*Blo) := hu
      _≤U*(1+A*B) := mul_le_mul_of_nonneg_left (by linarith) hU

"""

base20 = ROOT / "Kobon/BBLTangentBounds.lean"
base48 = ROOT / "Kobon/BBLTangent48Bounds.lean"
known = {3:(existing(base20,"tan_1_bounds"),"BBLTangentBounds.tan_1_bounds","1*π/20"),
         6:(existing(base20,"tan_2_bounds"),"BBLTangentBounds.tan_2_bounds","2*π/20"),
         9:(existing(base20,"tan_3_bounds"),"BBLTangentBounds.tan_3_bounds","3*π/20"),
         10:(existing(base48,"tan_6_1_bounds"),"BBLTangent48Bounds.tan_6_1_bounds","1*π/6"),
         12:(existing(base20,"tan_4_bounds"),"BBLTangentBounds.tan_4_bounds","4*π/20"),
         15:((F(1),F(1)),None,"π/4"),
         18:(existing(base20,"tan_6_bounds"),"BBLTangentBounds.tan_6_bounds","6*π/20"),
         20:(existing(base48,"tan_3_1_bounds"),"BBLTangent48Bounds.tan_3_1_bounds","1*π/3"),
         21:(existing(base20,"tan_7_bounds"),"BBLTangentBounds.tan_7_bounds","7*π/20"),
         24:(existing(base20,"tan_8_bounds"),"BBLTangentBounds.tan_8_bounds","8*π/20"),
         27:(existing(base20,"tan_9_bounds"),"BBLTangentBounds.tan_9_bounds","9*π/20"),
         5:(existing(base48,"tan_12_1_bounds"),"BBLTangent48Bounds.tan_12_1_bounds","1*π/12")}
bounds = {k:known[k][0] for k in known}
text = header
for k, (iv, declaration, angle) in known.items():
    text += f"theorem tan_{k}_bounds : {rat(iv[0])}≤tan ({k}*π/60) ∧ tan ({k}*π/60)≤{rat(iv[1])} := by\n"
    text += f"  have heq : {k}*π/60={angle} := by ring\n  rw [heq]\n"
    text += "  rw [tan_pi_div_four]\n  norm_num\n\n" if declaration is None else f"  convert {declaration} using 1 <;> norm_num\n\n"


def write_sub(k, ka, kb):
    global text
    iv = bounds[k] = sub(bounds[ka], bounds[kb])
    al, au = bounds[ka]
    bl, bu = bounds[kb]
    text += f"theorem tan_{k}_bounds : {rat(iv[0])}≤tan ({k}*π/60) ∧ tan ({k}*π/60)≤{rat(iv[1])} := by\n"
    text += f"  have heq : {k}*π/60={ka}*π/60-{kb}*π/60 := by ring\n  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]\n"
    text += f"  obtain ⟨hAl,hAu⟩ := tan_{ka}_bounds\n  obtain ⟨hBl,hBu⟩ := tan_{kb}_bounds\n"
    text += f"  exact subtraction_bounds _ _ {rat(al)} {rat(au)} {rat(bl)} {rat(bu)} _ _\n    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)\n    (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n\n"


write_sub(2,12,10)
# Exact Taylor enclosures propose a candidate; half_bounds proves it from
# the already checked double-angle interval.
spec=importlib.util.spec_from_file_location("uniform49",ROOT / "experiments/2026-10-02/verify_uniform_grid49.py")
u=importlib.util.module_from_spec(spec)
spec.loader.exec_module(u)
pi=u.dyadic(u.add(u.scale(u.atan_bound(F(1,5)),16),u.scale(u.atan_bound(F(1,239)),-4)),200)
bounds[1]=rounded(u.divide(u.trig_bound(u.scale(pi,F(1,60)),True),u.trig_bound(u.scale(pi,F(1,60)),False)),22)
iv=bounds[1]; al,au=bounds[2]
text += f"theorem tan_1_bounds : {rat(iv[0])}≤tan (1*π/60) ∧ tan (1*π/60)≤{rat(iv[1])} := by\n"
text += "  obtain ⟨hp,hu⟩ := tan_small (1*π/60) (by linarith [pi_pos]) (by linarith [pi_pos])\n  have hid := tan_half_identity (1*π/60) (by linarith [pi_pos]) (by linarith [pi_pos])\n  have heq : 2*(1*π/60)=2*π/60 := by ring\n  rw [heq] at hid\n  obtain ⟨hAl,hAu⟩ := tan_2_bounds\n"
text += f"  exact half_bounds _ _ _ _ {rat(al)} {rat(au)} hp hu (by linarith) hAl hAu\n    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hid (by norm_num) (by norm_num)\n\n"
for k,ka,kb in [(4,10,6),(7,10,3),(8,12,4),(11,12,1),(13,15,2),(14,15,1)]:
    write_sub(k,ka,kb)
for k in [16,17,19,22,23,25,26,28,29]:
    j=30-k
    iv=bounds[k]=rounded((1/bounds[j][1],1/bounds[j][0]),20)
    text += f"theorem tan_{k}_bounds : {rat(iv[0])}≤tan ({k}*π/60) ∧ tan ({k}*π/60)≤{rat(iv[1])} := by\n"
    text += f"  have heq : {k}*π/60=π/2-{j}*π/60 := by ring\n  rw [heq,tan_pi_div_two_sub]\n  obtain ⟨hl,hu⟩ := tan_{j}_bounds\n  have hp : 0<tan ({j}*π/60) := by linarith\n  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)\n  · nlinarith\n  · nlinarith\n\n"
text += "#print axioms tan_1_bounds\n#print axioms tan_29_bounds\nend Kobon.BBLTangent60Bounds\n"
(OUT / "BBLTangent60Bounds.lean").write_text(text,encoding="utf8")
(OUT / "bounds.json").write_text(json.dumps({str(k):[str(x) for x in bounds[k]] for k in sorted(bounds)},indent=2)+"\n")
print(json.dumps(dict(draft=str(OUT / "BBLTangent60Bounds.lean"),angles=len(bounds))))
