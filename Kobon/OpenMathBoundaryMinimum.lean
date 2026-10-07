import Kobon.OpenMathQuantitativeSuccessor

/-! A parity-independent positive boundary resource.  Every admissible normal
has a maximal old vertex with two forward-positive terminal rays.  Exact
normal-sector double counting therefore forces at least three actual
double-terminal vertices, even when the segment-deficit estimate is zero. -/
namespace Kobon.OpenMathBoundaryMinimum
open Cells FanGeometry UpperVertexBudget UpperEdgeInventory
  OpenMathSimpleBoundary OpenMathBoundaryNormals OpenMathBoundaryRays
  OpenMathBoundaryChart OpenMathBoundarySectorGeometry OpenMathBoundarySignedSamples
  OpenMathBoundaryWitnesses OpenMathBoundaryVisibility OpenMathBoundarySuccessor
  OpenMathBoundaryDoubleCounting Exterior Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem projection_parameter_difference (l w : Line ℝ) (x y : ℝ) :
    projection w (parameter l y)-projection w (parameter l x)=
      projection w (coordinateRay l 1)*(y-x) := by
  by_cases hb : l.b=0
  · simp only [parameter,coordinateRay,hb,if_true,if_false,projection]
    ring
  · simp only [parameter,coordinateRay,hb,if_true,if_false,projection]
    field_simp
    ring

theorem projection_coordinate_difference (l w : Line ℝ) (valid : l.a≠0 ∨ l.b≠0)
    (p q : Point) (hp : affineEval l p=0) (hq : affineEval l q=0) :
    projection w q-projection w p=projection w (coordinateRay l 1)*
      (coordinate l q-coordinate l p) := by
  have h := projection_parameter_difference l w (coordinate l p) (coordinate l q)
  rw [parameter_coordinate l valid p hp,parameter_coordinate l valid q hq] at h
  exact h

theorem terminal_of_max_projection (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hn : 2≤n) (i : Fin n) (w : Line ℝ)
    (hw : det (L i) w≠0) (p : Point) (hpi : p∈onLine n L i)
    (hmax : ∀ q∈onLine n L i, projection w q≤projection w p) :
    p∈lineTerminals n L i := by
  classical
  obtain ⟨k,rfl⟩ := orderedPoint_surjective n L hp hn i hpi
  apply (terminal_index_iff n L i k).mpr
  let c := projection w (coordinateRay (L i) 1)
  have hc : c≠0 := coordinateRay_transverse _ _ (by norm_num) hw
  have hm : 0<(coordinates n L i).card := by have := k.isLt; omega
  rcases lt_or_gt_of_ne hc with hneg|hpos
  · left
    by_contra hk
    let j : Fin (coordinates n L i).card := ⟨0,hm⟩
    have hjk : j<k := by change 0<k.val; omega
    have hcoord : coordinate (L i) (orderedPoint n L i j)<
        coordinate (L i) (orderedPoint n L i k) := by
      simp only [orderedPoint,coordinate_parameter]
      exact ((coordinates n L i).orderEmbOfFin rfl).strictMono hjk
    have he := projection_coordinate_difference (L i) w (line_valid n L hp hn i)
      (orderedPoint n L i k) (orderedPoint n L i j)
      (mem_filter.mp (orderedPoint_mem n L hp hn i k)).2
      (mem_filter.mp (orderedPoint_mem n L hp hn i j)).2
    have hpos' := mul_pos_of_neg_of_neg hneg (sub_neg.mpr hcoord)
    have hh := hmax _ (orderedPoint_mem n L hp hn i j)
    change projection w (orderedPoint n L i j)-projection w (orderedPoint n L i k)=
      c*(coordinate (L i) (orderedPoint n L i j)-coordinate (L i) (orderedPoint n L i k)) at he
    linarith
  · right
    by_contra hk
    let j : Fin (coordinates n L i).card := ⟨(coordinates n L i).card-1,by omega⟩
    have hkj : k<j := by change k.val<(coordinates n L i).card-1; have := k.isLt; omega
    have hcoord : coordinate (L i) (orderedPoint n L i k)<
        coordinate (L i) (orderedPoint n L i j) := by
      simp only [orderedPoint,coordinate_parameter]
      exact ((coordinates n L i).orderEmbOfFin rfl).strictMono hkj
    have he := projection_coordinate_difference (L i) w (line_valid n L hp hn i)
      (orderedPoint n L i k) (orderedPoint n L i j)
      (mem_filter.mp (orderedPoint_mem n L hp hn i k)).2
      (mem_filter.mp (orderedPoint_mem n L hp hn i j)).2
    have hpos' := mul_pos hpos (sub_pos.mpr hcoord)
    have hh := hmax _ (orderedPoint_mem n L hp hn i j)
    change projection w (orderedPoint n L i j)-projection w (orderedPoint n L i k)=
      c*(coordinate (L i) (orderedPoint n L i j)-coordinate (L i) (orderedPoint n L i k)) at he
    linarith

theorem maximal_vertex_double (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 3≤n)
    (w : Line ℝ) (hw : Admissible n L w) (p : Point) (hpv : p∈vertices n L)
    (hmax : ∀ q∈vertices n L,projection w q≤projection w p) :
    p∈doubleTerminals n L := by
  classical
  obtain ⟨i,j,hij,hspan⟩ := simple_ordinary n L hp hs hpv
  have hpi : p∈onLine n L i := mem_filter.mpr ⟨hpv,(hspan i).mpr (Or.inl rfl)⟩
  have hpj : p∈onLine n L j := mem_filter.mpr ⟨hpv,(hspan j).mpr (Or.inr rfl)⟩
  have hi := terminal_of_max_projection n L hp (by omega) i w (hw i) p hpi
    (fun q hq => hmax q (mem_filter.mp hq).1)
  have hj := terminal_of_max_projection n L hp (by omega) j w (hw j) p hpj
    (fun q hq => hmax q (mem_filter.mp hq).1)
  have hsub : ({i,j} : Finset (Fin n))⊆terminalsAt n L p := by
    intro r hr
    rcases mem_insert.mp hr with rfl|hr
    · exact mem_filter.mpr ⟨mem_univ _,hi⟩
    · rw [mem_singleton] at hr
      subst r
      exact mem_filter.mpr ⟨mem_univ _,hj⟩
  have hlow := card_le_card hsub
  rw [card_pair hij] at hlow
  have hup := terminalsAt_le_two n L hp (by omega) (simple_ordinary n L hp hs hpv)
  exact mem_filter.mpr ⟨hpv,by omega⟩

theorem exists_third_index (n : Nat) (hn : 3≤n) (i j : Fin n) :
    ∃ r : Fin n, r≠i ∧ r≠j := by
  classical
  have hnot : ¬(univ : Finset (Fin n))⊆{i,j} := by
    intro h
    have hh := card_le_card h
    have hpair : ({i,j} : Finset (Fin n)).card≤2 := by
      by_cases he : i=j <;> simp [he]
    simp only [card_univ,Fintype.card_fin] at hh
    omega
  obtain ⟨r,hr,hrnot⟩ := not_subset.mp hnot
  exact ⟨r,by simpa only [mem_insert,mem_singleton,not_or] using hrnot⟩

theorem tangent_positive_at_maximum (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hn : 3≤n)
    {p : Point} (i j : Fin n) (hij : i≠j) (vertex : intersection (L i) (L j)=p)
    (transverse : ∀ r : Fin n, r≠i → r≠j → affineEval (L r) p≠0)
    (w : Line ℝ) (hw : Admissible n L w)
    (hmax : ∀ q∈vertices n L,projection w q≤projection w p)
    (d : Point) (hd : d≠(0,0)) (htan : projection (L i) d=0)
    (hsg : TerminalSigns n L p d) : 0<projection w d := by
  classical
  obtain ⟨r,hri,hrj⟩ := exists_third_index n hn i j
  have hir : i≠r := hri.symm
  have hdij := BBLExtrema.det_ne_of_ne n L hp i j hij
  have hdri := BBLExtrema.det_ne_of_ne n L hp i r hir
  let q := intersection (L i) (L r)
  have hqv : q∈vertices n L := mem_image.mpr
    ⟨(i,r),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hir⟩,rfl⟩
  have hpi : affineEval (L i) p=0 := by simpa only [vertex] using intersection_on_left _ _ hdij
  have hqi : affineEval (L i) q=0 := intersection_on_left _ _ hdri
  have hwr : det w (L i)≠0 := by rw [HybridBoundary.det_skew]; exact neg_ne_zero.mpr (hw i)
  have hproj : projection w q<projection w p := by
    have hle := hmax q hqv
    apply lt_of_le_of_ne hle
    intro he
    have hpq : p=q := by
      apply two_lines_two_points (L i) (levelLine w (projection w p)) p q (hw i) hpi hqi
      · simp [level_eval]
      · rw [level_eval,he]
        ring
    have hrp := transverse r hri hrj
    rw [hpq] at hrp
    exact hrp (intersection_on_right _ _ hdri)
  have hP : projection w d≠0 := projection_nonzero_transverse (L i) w d (hw i) hd htan
  have hE : affineEval (L r) p≠0 := transverse r hri hrj
  have hED := hsg r hE
  have hD : projection (L r) d≠0 := by intro h; rw [h,mul_zero] at hED; linarith
  have heval := BBLExtrema.evaluation_from_intersection (L r) (L i) (L j) w
    hdij hdri hwr
  rw [vertex,tangent_derivative _ _ _ _ htan hwr hP] at heval
  have hid : (affineEval (L r) p*projection (L r) d)*projection w d=
      (projection (L r) d)^2*(projection w p-projection w q) := by
    rw [heval]
    dsimp [q]
    field_simp
  have hpositive := mul_pos (sq_pos_of_ne_zero hD) (sub_pos.mpr hproj)
  rw [←hid] at hpositive
  exact (mul_pos_iff_of_pos_left hED).mp hpositive

theorem normal_selects_vertex (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 3≤n)
    (a : Fin n × Bool) : 1≤selectedCount (selected n L hp (by omega)) a := by
  classical
  let w := normal n L hp (by omega) a
  have hw : Admissible n L w := normal_admissible n L hp (by omega) a
  have hne : (vertices n L).Nonempty := by
    obtain ⟨p,hp⟩ := onLine_nonempty n L hp (by omega) ⟨0,by omega⟩
    exact ⟨p,(mem_filter.mp hp).1⟩
  obtain ⟨p,hpv,hmax⟩ := exists_max_image (vertices n L) (projection w) hne
  have hdouble := maximal_vertex_double n L hp hs hn w hw p hpv hmax
  let v : {p : Point // p∈doubleTerminals n L} := ⟨p,hdouble⟩
  let W := witness n L hp (by omega) v
  have hd : 0<projection w W.first := tangent_positive_at_maximum n L hp hn
    W.i W.j (ne_of_lt W.ordered) W.vertex (W.transverse_eval hp hs) w hw hmax
    W.first W.first_ne W.first_tangent W.first_signs
  have hv : intersection (L W.j) (L W.i)=p :=
    (Exterior.intersection_swap _ _).trans W.vertex
  have he : 0<projection w W.second := tangent_positive_at_maximum n L hp hn
    W.j W.i (ne_of_lt W.ordered).symm hv (fun r hri hrj => W.transverse_eval hp hs r hrj hri)
    w hw hmax W.second W.second_ne W.second_tangent W.second_signs
  unfold selectedCount
  apply card_pos.mpr
  exact ⟨v,mem_filter.mpr ⟨mem_univ _,⟨hd,he⟩⟩⟩

/-- Every actual nonparallel simple arrangement with at least three lines
has at least three vertices that are terminal on both supporting lines. -/
theorem double_terminal_minimum (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 3≤n) :
    3≤(doubleTerminals n L).card := by
  classical
  let β := {p : Point // p∈doubleTerminals n L}
  letI : Fintype β := Finset.Subtype.fintype _
  have hmass := sum_selectedCount_eq (selected n L hp (by omega)) (n-1)
    (boundary_selection_degree n L hp hs (by omega))
  have hlower : Fintype.card (Fin n × Bool)≤
      ∑ a : Fin n × Bool, selectedCount (selected n L hp (by omega)) a := by
    calc
      _=∑ _a : Fin n × Bool, (1 : Nat) := by simp
      _≤_ := sum_le_sum (fun a _ => normal_selects_vertex n L hp hs hn a)
  rw [hmass] at hlower
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe] at hlower
  by_contra h
  have hB : (doubleTerminals n L).card≤2 := by omega
  have hprod := Nat.mul_le_mul_left (n-1) hB
  have hpred : n-1+1=n := by omega
  nlinarith

#print axioms terminal_of_max_projection
#print axioms maximal_vertex_double
#print axioms tangent_positive_at_maximum
#print axioms normal_selects_vertex
#print axioms double_terminal_minimum
end Kobon.OpenMathBoundaryMinimum
