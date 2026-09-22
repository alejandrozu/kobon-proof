import Kobon.FurediPalasti
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
  | 3 => 1
  | 5 => 5
  | 6 => 7
  | 7 => 11
  | 8 => 15
  | 9 => 21
  | 10 => 25
  | 11 => 32
  | 12 => 38
  | 13 => 47
  | 14 => 54
  | 15 => 65
  | 16 => 72
  | 17 => 85
  | 18 => 93
  | 19 => 107
  | 20 => 117
  | 21 => 133
  | 22 => 143
  | 23 => 161
  | 24 => 172
  | 25 => 191
  | 26 => 204
  | 27 => 225
  | 28 => 238
  | 29 => 261
  | 30 => 275
  | 31 => 299
  | 32 => 315
  | 33 => 341
  | 34 => 357
  | 35 => 385
  | 36 => 402
  | 37 => 431
  | 38 => 450
  | 39 => 470
  | 41 => 533
  | 42 => 553
  | 43 => 587
  | 44 => 608
  | 45 => 645
  | 46 => 667
  | 47 => 691
  | 48 => 721
  | 49 => 767
  | 50 => 792
  | 51 => 818
  | 53 => 885
  | 54 => 919
  | 55 => 955
  | 57 => 1045
  | 58 => 1073
  | 59 => 1103
  | 60 => 1141
  | 65 => 1365
  | 66 => 1397
  | 81 => 2132
  | 82 => 2172
  | 99 => 3170
  | 129 => 5461
  | 130 => 5525
  | 161 => 8532
  | 162 => 8612
  | 195 => 12482
  | _ => 0

theorem enhancement_sound (n : ℕ) : LowerBound n (enhancement n) := by
  unfold enhancement
  split
  · exact Kobon.Certificates.N003T00001H05c82de6.lower_bound
  · exact Kobon.Certificates.N005T00005H948a0bdf.lower_bound
  · exact Kobon.Certificates.N006T00007H6ea9ebaa.lower_bound
  · exact Kobon.Certificates.N007T00011He6b9a626.lower_bound
  · exact Kobon.Certificates.N008T00015Ha1380810.lower_bound
  · exact Kobon.Certificates.N009T00021H6ebbed82.lower_bound
  · exact Kobon.Certificates.N010T00025Hb767c427.lower_bound
  · exact Kobon.Certificates.N011T00032Hb955e7c9.lower_bound
  · exact Kobon.Certificates.N012T00038H38f69f38.lower_bound
  · exact Kobon.Certificates.N013T00047Hddec1f78.lower_bound
  · exact Kobon.Certificates.N014T00054Hd47aea63.lower_bound
  · exact Kobon.Certificates.N015T00065H4d3bf3b4.lower_bound
  · exact Kobon.Certificates.N016T00072H391cf79a.lower_bound
  · exact Kobon.Certificates.N017T00085H7cf3c061.lower_bound
  · exact Kobon.Certificates.N018T00093Hedb6246a.lower_bound
  · exact Kobon.Certificates.N019T00107Ha2f32bdb.lower_bound
  · exact Kobon.Certificates.N020T00117H382171ac.lower_bound
  · exact Kobon.Certificates.N021T00133H36bae754.lower_bound
  · exact Kobon.Certificates.N022T00143H54396c64.lower_bound
  · exact Kobon.Certificates.N023T00161H969ad7d3.lower_bound
  · exact Kobon.Certificates.N024T00172He63e906b.lower_bound
  · exact Kobon.Certificates.N025T00191Hb568bffb.lower_bound
  · exact Kobon.Certificates.N026T00204Hf71379c4.lower_bound
  · exact Kobon.Certificates.N027T00225H7d6ae9a0.lower_bound
  · exact Kobon.Certificates.N028T00238H56ef2acb.lower_bound
  · exact Kobon.Certificates.N029T00261Hd4805c25.lower_bound
  · exact Kobon.Certificates.N030T00275Hdcfe649a.lower_bound
  · exact Kobon.Certificates.N031T00299H70f23b94.lower_bound
  · exact Kobon.Certificates.N032T00315H5914f2bb.lower_bound
  · exact Kobon.Certificates.N033T00341H95f3b770.lower_bound
  · exact Kobon.Certificates.N034T00357Hfbde0a76.lower_bound
  · exact Kobon.Certificates.N035T00385H9ee99af6.lower_bound
  · exact Kobon.Certificates.N036T00402H3fc01b7d.lower_bound
  · exact Kobon.Certificates.N037T00431H11f0bde7.lower_bound
  · exact Kobon.Certificates.N038T00450H8ba2bdb1.lower_bound
  · exact Kobon.Certificates.N039T00470H30caa6f7.lower_bound
  · exact Kobon.Certificates.N041T00533H01e2ef66.lower_bound
  · exact Kobon.Certificates.N042T00553H2bdc9d67.lower_bound
  · exact Kobon.Certificates.N043T00587H861d8be2.lower_bound
  · exact Kobon.Certificates.N044T00608Hb5277675.lower_bound
  · exact Kobon.Certificates.N045T00645H3dc6e882.lower_bound
  · exact Kobon.Certificates.N046T00667H32b8ca2f.lower_bound
  · exact Kobon.Certificates.N047T00691Hfac44af1.lower_bound
  · exact Kobon.Certificates.N048T00721H2fb5ef0d.lower_bound
  · exact Kobon.Certificates.N049T00767H957e6f15.lower_bound
  · exact Kobon.Certificates.N050T00792H3d40cb58.lower_bound
  · exact Kobon.Certificates.N051T00818Hc18e1baf.lower_bound
  · exact Kobon.Certificates.N053T00885H6bc5b14d.lower_bound
  · exact Kobon.Certificates.N054T00919Ha254c1b4.lower_bound
  · exact Kobon.Certificates.N055T00955H202625a3.lower_bound
  · exact Kobon.Certificates.N057T01045H9a1d337c.lower_bound
  · exact Kobon.Certificates.N058T01073Hd988db55.lower_bound
  · exact Kobon.Certificates.N059T01103Hba482375.lower_bound
  · exact Kobon.Certificates.N060T01141H9bc5096c.lower_bound
  · exact Kobon.Certificates.N065T01365Hb1dcbeb4.lower_bound
  · exact Kobon.Certificates.N066T01397H327ecbb9.lower_bound
  · exact Kobon.Certificates.N081T02132H7bc6b303.lower_bound
  · exact Kobon.Certificates.N082T02172Hd75c9101.lower_bound
  · exact Kobon.Certificates.N099T03170Hea507e2d.lower_bound
  · exact Kobon.Certificates.N129T05461H6dae0012.lower_bound
  · exact Kobon.Certificates.N130T05525He0559b54.lower_bound
  · exact Kobon.Certificates.N161T08532H230691d5.lower_bound
  · exact Kobon.Certificates.N162T08612H1512e696.lower_bound
  · exact Kobon.Certificates.N195T12482H5413dd7b.lower_bound
  · exact zero_lower_bound n

def bound (n : ℕ) : ℕ := max (baseline n) (enhancement n)

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

theorem exact_exception_values :
    bound 3=1 ∧
    bound 5=5 ∧
    bound 6=7 ∧
    bound 7=11 ∧
    bound 8=15 ∧
    bound 9=21 ∧
    bound 10=25 ∧
    bound 11=32 ∧
    bound 12=38 ∧
    bound 13=47 ∧
    bound 14=54 ∧
    bound 15=65 ∧
    bound 16=72 ∧
    bound 17=85 ∧
    bound 18=93 ∧
    bound 19=107 ∧
    bound 20=117 ∧
    bound 21=133 ∧
    bound 22=143 ∧
    bound 23=161 ∧
    bound 24=172 ∧
    bound 25=191 ∧
    bound 26=204 ∧
    bound 27=225 ∧
    bound 28=238 ∧
    bound 29=261 ∧
    bound 30=275 ∧
    bound 31=299 ∧
    bound 32=315 ∧
    bound 33=341 ∧
    bound 34=357 ∧
    bound 35=385 ∧
    bound 36=402 ∧
    bound 37=431 ∧
    bound 38=450 ∧
    bound 39=470 ∧
    bound 41=533 ∧
    bound 42=553 ∧
    bound 43=587 ∧
    bound 44=608 ∧
    bound 45=645 ∧
    bound 46=667 ∧
    bound 47=691 ∧
    bound 48=721 ∧
    bound 49=767 ∧
    bound 50=792 ∧
    bound 51=818 ∧
    bound 53=885 ∧
    bound 54=919 ∧
    bound 55=955 ∧
    bound 57=1045 ∧
    bound 58=1073 ∧
    bound 59=1103 ∧
    bound 60=1141 ∧
    bound 65=1365 ∧
    bound 66=1397 ∧
    bound 81=2132 ∧
    bound 82=2172 ∧
    bound 99=3170 ∧
    bound 129=5461 ∧
    bound 130=5525 ∧
    bound 161=8532 ∧
    bound 162=8612 ∧
    bound 195=12482 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem dominates_every_saved_certificate :
    1 ≤ bound 3 ∧
    2 ≤ bound 4 ∧
    5 ≤ bound 5 ∧
    7 ≤ bound 6 ∧
    11 ≤ bound 7 ∧
    14 ≤ bound 8 ∧
    21 ≤ bound 9 ∧
    25 ≤ bound 10 ∧
    32 ≤ bound 11 ∧
    38 ≤ bound 12 ∧
    47 ≤ bound 13 ∧
    53 ≤ bound 14 ∧
    65 ≤ bound 15 ∧
    72 ≤ bound 16 ∧
    85 ≤ bound 17 ∧
    93 ≤ bound 18 ∧
    107 ≤ bound 19 ∧
    116 ≤ bound 20 ∧
    133 ≤ bound 21 ∧
    143 ≤ bound 22 ∧
    161 ≤ bound 23 ∧
    172 ≤ bound 24 ∧
    191 ≤ bound 25 ∧
    203 ≤ bound 26 ∧
    225 ≤ bound 27 ∧
    238 ≤ bound 28 ∧
    261 ≤ bound 29 ∧
    275 ≤ bound 30 ∧
    299 ≤ bound 31 ∧
    314 ≤ bound 32 ∧
    341 ≤ bound 33 ∧
    357 ≤ bound 34 ∧
    385 ≤ bound 35 ∧
    402 ≤ bound 36 ∧
    431 ≤ bound 37 ∧
    449 ≤ bound 38 ∧
    469 ≤ bound 39 ∧
    494 ≤ bound 40 ∧
    533 ≤ bound 41 ∧
    553 ≤ bound 42 ∧
    587 ≤ bound 43 ∧
    608 ≤ bound 44 ∧
    645 ≤ bound 45 ∧
    667 ≤ bound 46 ∧
    690 ≤ bound 47 ∧
    720 ≤ bound 48 ∧
    767 ≤ bound 49 ∧
    791 ≤ bound 50 ∧
    817 ≤ bound 51 ∧
    850 ≤ bound 52 ∧
    884 ≤ bound 53 ∧
    918 ≤ bound 54 ∧
    954 ≤ bound 55 ∧
    990 ≤ bound 56 ∧
    1045 ≤ bound 57 ∧
    1073 ≤ bound 58 ∧
    1102 ≤ bound 59 ∧
    1140 ≤ bound 60 ∧
    37 ≤ bound 12 ∧
    468 ≤ bound 39 ∧
    816 ≤ bound 51 ∧
    3 ≤ bound 5 ∧
    4 ≤ bound 6 ∧
    107 ≤ bound 19 ∧
    126 ≤ bound 21 ∧
    5 ≤ bound 5 ∧
    10 ≤ bound 7 ∧
    132 ≤ bound 21 ∧
    142 ≤ bound 22 ∧
    532 ≤ bound 41 ∧
    552 ≤ bound 42 ∧
    2132 ≤ bound 81 ∧
    2172 ≤ bound 82 ∧
    8532 ≤ bound 161 ∧
    8612 ≤ bound 162 ∧
    19 ≤ bound 9 ∧
    61 ≤ bound 15 ∧
    127 ≤ bound 21 ∧
    217 ≤ bound 27 ∧
    331 ≤ bound 33 ∧
    715 ≤ bound 48 ∧
    3169 ≤ bound 99 ∧
    12481 ≤ bound 195 ∧
    12480 ≤ bound 195 ∧
    602 ≤ bound 44 ∧
    3168 ≤ bound 99 ∧
    470 ≤ bound 39 ∧
    691 ≤ bound 47 ∧
    721 ≤ bound 48 ∧
    818 ≤ bound 51 ∧
    885 ≤ bound 53 ∧
    919 ≤ bound 54 ∧
    955 ≤ bound 55 ∧
    1103 ≤ bound 59 ∧
    1141 ≤ bound 60 ∧
    1365 ≤ bound 65 ∧
    1397 ≤ bound 66 ∧
    3170 ≤ bound 99 ∧
    5461 ≤ bound 129 ∧
    5525 ≤ bound 130 ∧
    12482 ≤ bound 195 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    54 ≤ bound 14 ∧
    52 ≤ bound 14 ∧
    53 ≤ bound 14 ∧
    52 ≤ bound 14 ∧
    52 ≤ bound 14 ∧
    14 ≤ bound 8 ∧
    51 ≤ bound 14 ∧
    114 ≤ bound 20 ∧
    203 ≤ bound 26 ∧
    313 ≤ bound 32 ∧
    448 ≤ bound 38 ∧
    791 ≤ bound 50 ∧
    15 ≤ bound 8 ∧
    54 ≤ bound 14 ∧
    117 ≤ bound 20 ∧
    204 ≤ bound 26 ∧
    315 ≤ bound 32 ∧
    402 ≤ bound 36 ∧
    450 ≤ bound 38 ∧
    553 ≤ bound 42 ∧
    792 ≤ bound 50 ∧
    107 ≤ bound 19 ∧
    6 ≤ bound 6 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem strict_improvements :
    baseline 3 < bound 3 ∧
    baseline 5 < bound 5 ∧
    baseline 6 < bound 6 ∧
    baseline 7 < bound 7 ∧
    baseline 8 < bound 8 ∧
    baseline 9 < bound 9 ∧
    baseline 10 < bound 10 ∧
    baseline 11 < bound 11 ∧
    baseline 12 < bound 12 ∧
    baseline 13 < bound 13 ∧
    baseline 14 < bound 14 ∧
    baseline 15 < bound 15 ∧
    baseline 16 < bound 16 ∧
    baseline 17 < bound 17 ∧
    baseline 18 < bound 18 ∧
    baseline 19 < bound 19 ∧
    baseline 20 < bound 20 ∧
    baseline 21 < bound 21 ∧
    baseline 22 < bound 22 ∧
    baseline 23 < bound 23 ∧
    baseline 24 < bound 24 ∧
    baseline 25 < bound 25 ∧
    baseline 26 < bound 26 ∧
    baseline 27 < bound 27 ∧
    baseline 28 < bound 28 ∧
    baseline 29 < bound 29 ∧
    baseline 30 < bound 30 ∧
    baseline 31 < bound 31 ∧
    baseline 32 < bound 32 ∧
    baseline 33 < bound 33 ∧
    baseline 34 < bound 34 ∧
    baseline 35 < bound 35 ∧
    baseline 36 < bound 36 ∧
    baseline 37 < bound 37 ∧
    baseline 38 < bound 38 ∧
    baseline 39 < bound 39 ∧
    baseline 41 < bound 41 ∧
    baseline 42 < bound 42 ∧
    baseline 43 < bound 43 ∧
    baseline 44 < bound 44 ∧
    baseline 45 < bound 45 ∧
    baseline 46 < bound 46 ∧
    baseline 47 < bound 47 ∧
    baseline 48 < bound 48 ∧
    baseline 49 < bound 49 ∧
    baseline 50 < bound 50 ∧
    baseline 51 < bound 51 ∧
    baseline 53 < bound 53 ∧
    baseline 54 < bound 54 ∧
    baseline 55 < bound 55 ∧
    baseline 57 < bound 57 ∧
    baseline 58 < bound 58 ∧
    baseline 59 < bound 59 ∧
    baseline 60 < bound 60 ∧
    baseline 65 < bound 65 ∧
    baseline 66 < bound 66 ∧
    baseline 81 < bound 81 ∧
    baseline 82 < bound 82 ∧
    baseline 99 < bound 99 ∧
    baseline 129 < bound 129 ∧
    baseline 130 < bound 130 ∧
    baseline 161 < bound 161 ∧
    baseline 162 < bound 162 ∧
    baseline 195 < bound 195 := by
  repeat' apply And.intro
  all_goals decide +kernel

theorem baseline_after_last_exception (n : ℕ) (hn : 195<n) :
    bound n=baseline n := by
  have he : enhancement n=0 := by
    unfold enhancement
    split <;> omega
  simp [bound,he]


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
