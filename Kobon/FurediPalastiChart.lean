import Kobon.FurediPalasti
import Kobon.Projective

/-! A projective chart of the classical simple trigonometric arrangement.
The rightmost vertex can be isolated from every other vertex.
-/
namespace Kobon.FurediPalastiChart
open FurediPalasti

noncomputable def vertexX (x y : ℝ) : ℝ :=
  Real.cos (2*x)+Real.cos (2*y)+Real.cos (2*x+2*y)
noncomputable def vertexY (x y : ℝ) : ℝ :=
  Real.sin (2*x)+Real.sin (2*y)-Real.sin (2*x+2*y)

theorem vertex_on_left (x y : ℝ) :
    Real.sin x*vertexX x y+Real.cos x*vertexY x y=Real.sin (3*x) := by
  have h1 := Real.sin_add x (2*x)
  have h2 := Real.sin_add x (2*y)
  have h3 := Real.sin_sub x (2*x+2*y)
  have e1 : x+2*x=3*x := by ring
  have e3 : x-(2*x+2*y)=-(x+2*y) := by ring
  rw [e1] at h1
  rw [e3,Real.sin_neg] at h3
  dsimp [vertexX,vertexY]
  nlinarith

theorem intersection_x (x y : ℝ) (hd : det (line x) (line y)≠0) :
    (intersection (line x) (line y)).1=vertexX x y := by
  have h1 := vertex_on_left x y
  have h2 := vertex_on_left y x
  have es : vertexX y x=vertexX x y := by simp [vertexX,add_comm,add_left_comm]
  have et : vertexY y x=vertexY x y := by simp [vertexY,add_comm,add_left_comm]
  rw [es,et] at h2
  dsimp [intersection]
  apply (div_eq_iff hd).mpr
  dsimp [vertex,det,line]
  linear_combination -(Real.cos y)*h1+(Real.cos x)*h2

theorem cos_angle_le {a t : ℝ} (ha : 0≤a)
    (hl : a≤t) (hh : t≤Real.pi-a) : Real.cos (2*t)≤Real.cos (2*a) := by
  by_cases ht : t≤Real.pi/2
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  · have hp := Real.cos_le_cos_of_nonneg_of_le_pi
      (x:=2*a) (y:=2*Real.pi-2*t) (by linarith) (by linarith) (by linarith)
    simpa only [Real.cos_two_pi_sub] using hp

theorem cos_angle_lt {a t : ℝ} (ha : 0≤a)
    (hl : a<t) (hh : t<Real.pi-a) : Real.cos (2*t)<Real.cos (2*a) := by
  by_cases ht : t≤Real.pi/2
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  · have hp := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x:=2*a) (y:=2*Real.pi-2*t) (by linarith) (by linarith) (by linarith)
    simpa only [Real.cos_two_pi_sub] using hp

theorem angle_zero (n : ℕ) : angle n 0=Real.pi/(2*n) := by
  dsimp [angle]
  ring

theorem angle_last (n : ℕ) (hn : 0<n) :
    angle n (n-1)=Real.pi-angle n 0 := by
  have hcast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hnR : (n:ℝ)≠0 := by positivity
  dsimp [angle]
  rw [hcast]
  field_simp
  ring

theorem angle_le_angle {n i j : ℕ} (hn : 0<n) (hij : i≤j) : angle n i≤angle n j := by
  rcases hij.eq_or_lt with he | he
  · simp [he]
  · exact (angle_strictMono hn he).le

theorem index_cos_le {n i : ℕ} (hi : i<n) :
    Real.cos (2*angle n i)≤Real.cos (2*angle n 0) := by
  have hn : 0<n := by omega
  apply cos_angle_le (angle_pos hn).le (angle_le_angle hn (by omega))
  rw [← angle_last n hn]
  exact angle_le_angle hn (by omega)

theorem index_cos_lt {n i : ℕ} (hi : 0 < i) (hil : i < n-1) :
    Real.cos (2*angle n i)<Real.cos (2*angle n 0) := by
  have hn : 0<n := by omega
  apply cos_angle_lt (angle_pos hn).le (angle_strictMono hn hi)
  rw [← angle_last n hn]
  exact angle_strictMono hn hil

noncomputable def cap (n : ℕ) : ℝ := 1+2*Real.cos (2*angle n 0)

theorem cap_vertex (n : ℕ) (hn : 2≤n) :
    (intersection (arrangement n 0) (arrangement n (n-1))).1=cap n := by
  have hn0 : 0<n := by omega
  have hd : det (arrangement n 0) (arrangement n (n-1))≠0 :=
    noParallel n ⟨0,hn0⟩ ⟨n-1,by omega⟩ (by change 0<n-1; omega)
  rw [arrangement,arrangement,intersection_x _ _ hd]
  rw [vertexX,angle_last n hn0]
  have h1 : 2*(Real.pi-angle n 0)=2*Real.pi-2*angle n 0 := by ring
  have h2 : 2*angle n 0+(2*Real.pi-2*angle n 0)=2*Real.pi := by ring
  rw [h1,h2,Real.cos_two_pi_sub,Real.cos_two_pi]
  dsimp [cap]
  ring

theorem below_cap {n i j : ℕ} (hij : i<j) (hj : j<n)
    (hne : i≠0 ∨ j≠n-1) :
    (intersection (arrangement n i) (arrangement n j)).1<cap n := by
  have hi : i<n := by omega
  have hd := noParallel n ⟨i,hi⟩ ⟨j,hj⟩ hij
  rw [arrangement,arrangement,intersection_x _ _ hd]
  have h1 := index_cos_le hi
  have h2 := index_cos_le hj
  have h3 := Real.cos_le_one (2*angle n i+2*angle n j)
  dsimp [vertexX,cap]
  rcases hne with he | he
  · have h4 := index_cos_lt (by omega : 0 < i) (by omega : i < n-1)
    linarith
  · have h4 := index_cos_lt (by omega : 0 < j) (by omega : j < n-1)
    linarith

theorem cap_pos (n : ℕ) (hn : 3≤n) : 0<cap n := by
  have ha : 0≤2*angle n 0 := by have := angle_pos (i:=0) (by omega : 0<n); linarith
  have hb : 2*angle n 0≤Real.pi/2 := by
    rw [angle_zero]
    have hnR : (0:ℝ)<n := by positivity
    have hn2 : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith [Real.pi_pos]
  have hc := Real.cos_nonneg_of_mem_Icc (show 2*angle n 0 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by
    constructor <;> linarith [Real.pi_pos])
  dsimp [cap]
  linarith

theorem exists_cut (n : ℕ) (hn : 3≤n) :
    ∃ h : ℝ, 0<h ∧ h<cap n ∧
      ∀ i j : Fin n, i<j → (i.val≠0 ∨ j.val≠n-1) →
        (intersection (arrangement n i) (arrangement n j)).1<h := by
  classical
  let f : Fin n × Fin n → ℝ := fun p =>
    if p.1<p.2 ∧ (p.1.val≠0 ∨ p.2.val≠n-1)
    then (intersection (arrangement n p.1) (arrangement n p.2)).1 else 0
  have hn0 : 0<n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0,hn0⟩⟩
  have hf : ∀ p, f p<cap n := by
    intro p
    dsimp [f]
    split
    · rename_i h
      exact below_cap h.1 p.2.isLt h.2
    · exact cap_pos n hn
  let M := Finset.univ.sup' Finset.univ_nonempty f
  have hM : M<cap n := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun p _ => hf p)
  have hz : 0≤M := by
    have hle := Finset.le_sup' f (Finset.mem_univ ((⟨0,hn0⟩:Fin n),(⟨0,hn0⟩:Fin n)))
    simpa only [f,lt_self_iff_false,false_and,ite_false] using hle
  rcases exists_between hM with ⟨h,hMh,hh⟩
  refine ⟨h,lt_of_le_of_lt hz hMh,hh,?_⟩
  intro i j hij hne
  have hle := Finset.le_sup' f (Finset.mem_univ (i,j))
  have hfij : f (i,j)=(intersection (arrangement n i) (arrangement n j)).1 := by
    simp [f,hij,hne]
  rw [hfij] at hle
  exact lt_of_le_of_lt hle hMh

end Kobon.FurediPalastiChart
