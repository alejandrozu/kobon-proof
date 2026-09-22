"""Generate the finite enhancement of the separately proved all-order baseline.

The catalogue is not trusted: generated theorem terms cite checked geometric
witnesses, and the comparison against every catalogue entry is kernel checked.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def main():
    records = json.loads((ROOT / 'verification/certificate-index.json').read_text())
    best = {}
    for row in records:
        n = row['n']
        if n not in best or row['triangles'] > best[n]['triangles']:
            best[n] = row
    selected = [d for n, d in sorted(best.items())
                if d['triangles'] > (n * max(0, n-3) + 2)//3]
    body = '''import Kobon.FurediPalasti
import Kobon.Results

/-! An unconditional lower bound for EVERY natural order. The quadratic
baseline is the classical Furedi--Palasti construction, geometrically proved
in this library. Finite improvements retain the provenance of their witnesses.
No unrestricted full-gain recurrence or BBL iteration is assumed.
-/
namespace Kobon.AllN

theorem zero_lower_bound (n : ℕ) : LowerBound n 0 := by
  refine ⟨(fun i => ⟨(i:ℝ),1,0⟩),?_,[],by simp,by simp,by simp⟩
  intro i j hij
  change (i.val:ℝ)*1-1*(j.val:ℝ) ≠ 0
  simp only [mul_one,one_mul]
  apply sub_ne_zero.mpr
  exact ne_of_lt (by exact_mod_cast hij)

def baseline (n : ℕ) : ℕ := (n*(n-3)+2)/3

theorem baseline_sound (n : ℕ) : LowerBound n (baseline n) := by
  by_cases hn : 3≤n
  · exact FurediPalasti.lower_bound n hn
  · have he : baseline n=0 := by
      unfold baseline
      have : n-3=0 := by omega
      simp [this]
    rw [he]
    exact zero_lower_bound n

/-- Exactly the certified exceptions which strictly improve the baseline. -/
def enhancement : ℕ → ℕ
'''
    for d in selected:
        body += f"  | {d['n']} => {d['triangles']}\n"
    body += '  | _ => 0\n\n'
    body += 'theorem enhancement_sound (n : ℕ) : LowerBound n (enhancement n) := by\n'
    body += '  unfold enhancement\n  split\n'
    for d in selected:
        body += f"  · exact {d['theorem']}\n"
    body += '  · exact zero_lower_bound n\n\n'
    body += '''def bound (n : ℕ) : ℕ := max (baseline n) (enhancement n)

/-- The main all-order geometric existence theorem, without geometric premises. -/
theorem all_n (n : ℕ) : LowerBound n (bound n) := by
  unfold bound
  rcases le_total (baseline n) (enhancement n) with h | h
  · rw [max_eq_right h]
    exact enhancement_sound n
  · rw [max_eq_left h]
    exact baseline_sound n

theorem baseline_le (n : ℕ) : baseline n ≤ bound n := Nat.le_max_left _ _
theorem enhancement_le (n : ℕ) : enhancement n ≤ bound n := Nat.le_max_right _ _

theorem floor_benchmark_le (n : ℕ) : n*(n-3)/3 ≤ bound n := by
  apply le_trans _ (baseline_le n)
  unfold baseline
  omega

'''
    checks = ' ∧\n    '.join(f"bound {d['n']}={d['triangles']}" for d in selected)
    body += f"theorem exact_exception_values :\n    {checks} := by\n  repeat' apply And.intro\n  all_goals decide +kernel\n\n"
    checks = ' ∧\n    '.join(f"{d['triangles']} ≤ bound {d['n']}" for d in records)
    body += f"theorem dominates_every_saved_certificate :\n    {checks} := by\n  repeat' apply And.intro\n  all_goals decide +kernel\n\n"
    checks = ' ∧\n    '.join(f"baseline {d['n']} < bound {d['n']}" for d in selected)
    body += f"theorem strict_improvements :\n    {checks} := by\n  repeat' apply And.intro\n  all_goals decide +kernel\n\n"
    body += f'''theorem baseline_after_last_exception (n : ℕ) (hn : {max(d['n'] for d in selected)}<n) :
    bound n=baseline n := by
  have he : enhancement n=0 := by
    unfold enhancement
    split <;> omega
  simp [bound,he]

'''
    body += '''
/-- Arithmetic comparison with Tamura's polynomial, not a proof of that upper bound. -/
theorem polynomial_gap (n : ℕ) : n*(n-2)/3 ≤ bound n+n/3 := by
  by_cases hn : 3≤n
  · have h3 : n-3+3=n := by omega
    have h2 : n-2+2=n := by omega
    have he : n*(n-2)=n*(n-3)+n := by nlinarith
    have hb := baseline_le n
    unfold baseline at hb
    rw [he]
    omega
  · have hn' : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases hn' with rfl | rfl | rfl <;> norm_num [bound,baseline,enhancement]

theorem baseline_dominates_49_target (n : ℕ) (hn : 51≤n) :
    (n-1)^2/4+191 ≤ baseline n := by
  have h1 : n-1+1=n := by omega
  have h3 : n-3+3=n := by omega
  have hb : n*(n-3) ≤ 3*baseline n := by unfold baseline; omega
  have ht : 4*((n-1)^2/4) ≤ (n-1)^2 := by omega
  have hp := Nat.mul_le_mul_left n hn
  nlinarith

/-- The old 49-seed numerical target now follows unconditionally, without its recurrence. -/
theorem dominates_49_target (n : ℕ) (hn : 49≤n) :
    (n-1)^2/4+191 ≤ bound n := by
  by_cases h49 : n=49
  · subst n; decide +kernel
  by_cases h50 : n=50
  · subst n; decide +kernel
  exact le_trans (baseline_dominates_49_target n (by omega)) (baseline_le n)

theorem from_49_unconditional (n : ℕ) (hn : 49≤n) :
    LowerBound n ((n-1)^2/4+191) := by
  by_cases h49 : n=49
  · subst n; exact Results.classical_049
  by_cases h50 : n=50
  · subst n; exact Results.classical_050
  exact (baseline_sound n).mono (baseline_dominates_49_target n (by omega))

#print axioms baseline_sound
#print axioms all_n
#print axioms strict_improvements
#print axioms from_49_unconditional
end Kobon.AllN
'''
    (ROOT/'Kobon/AllN.lean').write_text(body, encoding='utf-8', newline='\n')
    out = ROOT/'research/all-n-formalization'
    out.mkdir(exist_ok=True)
    rows = [dict(n=d['n'], baseline=(d['n']*(d['n']-3)+2)//3,
                 lower_bound=d['triangles'], gain=d['triangles']-(d['n']*(d['n']-3)+2)//3,
                 theorem=d['theorem'], sources=d['sources']) for d in selected]
    (out/'exceptions.json').write_text(json.dumps(rows, indent=2)+'\n',
                                     encoding='utf-8', newline='\n')
    table = '# Complete finite enhancement table\n\n'
    table += (f'These are the {len(selected)} strict enhancements in this release, including prior '
              f'published constructions and reproductions. This is not a list of {len(selected)} '
              'new discoveries. At every unlisted order use the proved classical '
              'baseline. See [the report](README.md) for scope and attribution.\n\n')
    table += '| n | Baseline | Bound | Gain | Verified witness |\n|---:|---:|---:|---:|---|\n'
    for d in selected:
        n, t = d['n'], d['triangles']
        b = (n*(n-3)+2)//3
        table += f"| {n} | {b} | {t} | +{t-b} | [Lean](../../{d['lean_source']}) |\n"
    (out/'exceptions.md').write_text(table,encoding='utf-8',newline='\n')
    print(f'Generated an all-natural-order formula with {len(selected)} certified exceptions.')


if __name__ == '__main__':
    main()
