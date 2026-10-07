import Kobon.UpperOpenMathCutHalfplane
import Kobon.UpperCleanEdges

/-! At even order a triple-only arrangement has an odd number of ordinary
crossings on every indexed line, including lines through triple points.
The common half-plane argument remains valid at all those ordinary crossings.
These facts supply a parity route beyond clean-line charging; they do not
assume or assert a global token-payment inequality. -/
namespace Kobon.UpperOpenMathOrdinaryCutParity
open Cells FanGeometry UpperVertexBudget UpperSharedIncidence UpperCoreExtraction
  UpperCleanHalfplane UpperOpenMathCutHalfplane Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def ordinaryOnLine (n : ℕ) (L : ℕ → Line ℝ) (cut : Fin n) : Finset Point := by
  classical
  exact (onLine n L cut).filter (OrdinaryAt n L)

noncomputable def coreOnLine (n : ℕ) (L : ℕ → Line ℝ) (cut : Fin n) : Finset Point := by
  classical
  exact (onLine n L cut).filter (fun p => ¬OrdinaryAt n L p)

theorem crossing_fiber (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (cut : Fin n) (p : Point) (hp : p∈onLine n L cut) :
    ((univ : Finset (Fin n)).erase cut).filter
      (fun i : Fin n => intersection (L cut) (L i)=p)=(supports n L p).erase cut := by
  classical
  ext i
  simp only [mem_filter,mem_erase,mem_univ,true_and,and_true,supports]
  constructor
  · rintro ⟨hi,he⟩
    exact ⟨hi,(intersection_eq_iff n L hL cut i hi.symm p).mp he |>.2⟩
  · rintro ⟨hi,hpi⟩
    exact ⟨hi,(intersection_eq_iff n L hL cut i hi.symm p).mpr ⟨(mem_filter.mp hp).2,hpi⟩⟩

theorem crossing_weight_identity (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (cut : Fin n) :
    n-1=∑ p∈onLine n L cut, ((supports n L p).card-1) := by
  classical
  have h := card_eq_sum_card_image
    (fun i : Fin n => intersection (L cut) (L i)) ((univ : Finset (Fin n)).erase cut)
  rw [crossings_image n L hL cut] at h
  simp only [card_erase_of_mem (mem_univ cut),card_univ,Fintype.card_fin] at h
  rw [h]
  apply sum_congr rfl
  intro p hp
  rw [crossing_fiber n L hL cut p hp,card_erase_of_mem]
  exact mem_filter.mpr ⟨mem_univ cut,(mem_filter.mp hp).2⟩

theorem triple_ordinary_crossing_identity
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (cut : Fin n)
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    (ordinaryOnLine n L cut).card+2*(coreOnLine n L cut).card=n-1 := by
  classical
  have h := crossing_weight_identity n L hL cut
  have hterm (p : Point) (hp : p∈onLine n L cut) :
      (supports n L p).card-1=(if OrdinaryAt n L p then 1 else 2) := by
    by_cases ho : OrdinaryAt n L p
    · rw [(ordinary_iff_support_card n L p).mp ho,if_pos ho]
    · have hc : p∈core n L := mem_filter.mpr ⟨(mem_filter.mp hp).1,ho⟩
      rw [triples p hc,if_neg ho]
  rw [show (∑ p∈onLine n L cut, ((supports n L p).card-1))=
      ∑ p∈onLine n L cut, (if OrdinaryAt n L p then 1 else 2) from sum_congr rfl hterm] at h
  simp only [sum_ite,sum_const,nsmul_eq_mul,mul_one] at h
  simpa [ordinaryOnLine,coreOnLine,Nat.mul_comm] using h.symm

theorem triple_even_ordinary_crossings_odd
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (cut : Fin n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3) :
    (ordinaryOnLine n L cut).card%2=1 := by
  have h := triple_ordinary_crossing_identity n L hL cut triples
  have hn : 0<n := Nat.zero_lt_of_lt cut.isLt
  omega

theorem triple_even_no_ordinary_pair_partition
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (cut : Fin n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (pairs : Finset (Finset Point))
    (hpair : ∀ e∈pairs, e.card=2)
    (hdisj : (pairs : Set (Finset Point)).PairwiseDisjoint id)
    (hcover : pairs.biUnion id=ordinaryOnLine n L cut) : False := by
  classical
  have hcount := card_biUnion hdisj
  rw [hcover] at hcount
  dsimp only [id_eq] at hcount
  have hsum : (∑ e∈pairs, e.card)=pairs.card*2 := by
    calc
      _=∑ _e∈pairs, 2 := sum_congr rfl hpair
      _=pairs.card*2 := by simp
  rw [hsum] at hcount
  have hodd := triple_even_ordinary_crossings_odd n L hL cut heven triples
  omega

theorem ordinary_crossing_off_other
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (cut i k : Fin n) (hi : i≠cut) (hk : k≠cut) (hki : k≠i)
    (ho : OrdinaryAt n L (intersection (L cut) (L k))) :
    affineEval (L cut) (intersection (L i) (L k))≠0 := by
  intro hz
  have hd := noParallel_any n L hL i k i.isLt k.isLt (fun h => hki (Fin.ext h).symm)
  have he : intersection (L i) (L k)=intersection (L cut) (L k) :=
    (intersection_eq_iff n L hL cut k hk.symm _).mpr ⟨hz,intersection_on_right _ _ hd⟩ |>.symm
  have hpi : affineEval (L i) (intersection (L cut) (L k))=0 := by
    rw [← he]
    exact intersection_on_left _ _ hd
  have hcut := noParallel_any n L hL cut k cut.isLt k.isLt (fun h => hk (Fin.ext h).symm)
  have eq := ordinary_nonradial_unique n L _ ho cut k i
    (intersection_on_left _ _ hcut) (intersection_on_right _ _ hcut) hpi hk hi
  exact hki eq

theorem ordinary_crossings_common_side
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (notConcurrent : NotConcurrent n L) (cut : Fin n) :
    ∃ s : ℝ, (s=1 ∨ s= -1) ∧
      ∀ k : Fin n, k≠cut → OrdinaryAt n L (intersection (L cut) (L k)) → Witness n L cut s k := by
  rcases common_side_except_pencil n L hL notConcurrent cut with hpos|hneg
  · exact ⟨1,Or.inl rfl,fun k hk _ => hpos k hk⟩
  · obtain ⟨i,hi,hiw,all⟩ := hneg
    refine ⟨-1,Or.inr rfl,fun k hk ho => ?_⟩
    by_cases hki : k=i
    · simpa only [hki] using hiw
    · exact all k hk (Or.inr (ordinary_crossing_off_other n L hL cut i k hi hk hki ho))

#print axioms crossing_weight_identity
theorem not_concurrent_of_triples
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
    (triples : ∀ p∈core n L, (supports n L p).card=3) : NotConcurrent n L := by
  classical
  rintro ⟨p,hp⟩
  have hs : supports n L p=univ := by
    ext i
    simp only [supports,mem_filter,mem_univ,true_and]
    exact iff_true_intro (hp i)
  have hcard : (supports n L p).card=n := by rw [hs]; simp
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i≠j := by intro he; have hv := congrArg Fin.val he; dsimp [i,j] at hv; omega
  have he : intersection (L i) (L j)=p := (intersection_eq_iff n L hL i j hij p).mpr ⟨hp i,hp j⟩
  have hv : p∈vertices n L := mem_image.mpr ⟨(i,j),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hij⟩,he⟩
  have hno : ¬OrdinaryAt n L p := by
    intro ho
    have hh := (ordinary_iff_support_card n L p).mp ho
    omega
  have hc : p∈core n L := mem_filter.mpr ⟨hv,hno⟩
  have ht := triples p hc
  omega

theorem common_positive_cut_ordinary
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (notConcurrent : NotConcurrent n L) (line : Fin n) :
    ∃ cut : Line ℝ, (cut.a≠0 ∨ cut.b≠0) ∧
      (∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0) ∧
      ∀ i : Fin n, i≠line → OrdinaryAt n L (intersection (L line) (L i)) →
        ∃ q : Point, {intersection (L line) (L i),q}∈UpperEdgeInventory.lineEdges n L i ∧
          0<affineEval cut q := by
  classical
  obtain ⟨s,hs,hside⟩ := ordinary_crossings_common_side n L hL notConcurrent line
  have bounded (cut : Line ℝ) (he : ∀ p, affineEval cut p=s*affineEval (L line) p)
      (i : Fin n) (hi : i≠line) (ho : OrdinaryAt n L (intersection (L line) (L i))) :
      ∃ q : Point, {intersection (L line) (L i),q}∈UpperEdgeInventory.lineEdges n L i ∧
        0<affineEval cut q := by
    obtain ⟨j,hjl,hji,hj⟩ := hside i hi ho
    have hd := noParallel_any n L hL line i line.isLt i.isLt (fun h => hi (Fin.ext h).symm)
    have hid := noParallel_any n L hL i j i.isLt j.isLt (fun h => hji (Fin.ext h).symm)
    have hp : intersection (L line) (L i)∈onLine n L i := mem_filter.mpr
      ⟨UpperEdgeInventory.intersection_mem_vertices n L line i hi.symm,intersection_on_right _ _ hd⟩
    have hq : intersection (L i) (L j)∈onLine n L i := mem_filter.mpr
      ⟨UpperEdgeInventory.intersection_mem_vertices n L i j hji.symm,intersection_on_left _ _ hid⟩
    obtain ⟨q,hq',hedge,hpos⟩ := UpperCleanEdges.incident_positive_edge n L hL hn i cut _ _ hp hq
      (by rw [he,intersection_on_left _ _ hd,mul_zero]) (by rw [he]; exact hj)
    exact ⟨q,hedge,hpos⟩
  rcases hs with rfl|rfl
  · exact ⟨L line,Cells.line_valid n L hL hn line,fun _ => Iff.rfl,
      bounded (L line) (fun p => by simp)⟩
  · let cut : Line ℝ := ⟨-(L line).a,-(L line).b,-(L line).c⟩
    have he : ∀ p, affineEval cut p=(-1)*affineEval (L line) p := by
      intro p
      dsimp [cut,affineEval]
      ring
    refine ⟨cut,?_,?_,bounded cut he⟩
    · rcases Cells.line_valid n L hL hn line with ha|hb
      · exact Or.inl (neg_ne_zero.mpr ha)
      · exact Or.inr (neg_ne_zero.mpr hb)
    · intro p
      rw [he,neg_one_mul,neg_eq_zero]

theorem ordinary_endpoint_selectors
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (line : Fin n)
    (cut : Line ℝ)
    (hside : ∀ i : Fin n, i≠line → OrdinaryAt n L (intersection (L line) (L i)) →
      ∃ q : Point, {intersection (L line) (L i),q}∈UpperEdgeInventory.lineEdges n L i ∧
        0<affineEval cut q) :
    ∃ radial : Point → Fin n, ∃ tip : Point → Point,
      (∀ p∈ordinaryOnLine n L line, radial p≠line) ∧
      (∀ p∈ordinaryOnLine n L line, affineEval (L (radial p)) p=0) ∧
      (∀ p∈ordinaryOnLine n L line, {p,tip p}∈UpperEdgeInventory.lineEdges n L (radial p)) ∧
      (∀ p∈ordinaryOnLine n L line, 0<affineEval cut (tip p)) := by
  classical
  have cross (p : Point) (hp : p∈ordinaryOnLine n L line) :
      ∃ i : Fin n, i≠line ∧ intersection (L line) (L i)=p := by
    have hline := (mem_filter.mp hp).1
    rw [← crossings_image n L hL line] at hline
    obtain ⟨i,hi,he⟩ := mem_image.mp hline
    exact ⟨i,(mem_erase.mp hi).1,he⟩
  have hradchoice : ∀ p : Point, ∃ i : Fin n, p∈ordinaryOnLine n L line →
      i≠line ∧ intersection (L line) (L i)=p := by
    intro p
    by_cases hp : p∈ordinaryOnLine n L line
    · obtain ⟨i,hi,he⟩ := cross p hp
      exact ⟨i,fun _ => ⟨hi,he⟩⟩
    · exact ⟨line,fun hh => False.elim (hp hh)⟩
  choose radial hrad using hradchoice
  have htipchoice : ∀ p : Point, ∃ q : Point, p∈ordinaryOnLine n L line →
      {p,q}∈UpperEdgeInventory.lineEdges n L (radial p) ∧ 0<affineEval cut q := by
    intro p
    by_cases hp : p∈ordinaryOnLine n L line
    · have ho : OrdinaryAt n L (intersection (L line) (L (radial p))) := by
        rw [(hrad p hp).2]
        exact (mem_filter.mp hp).2
      obtain ⟨q,hq,hpos⟩ := hside (radial p) (hrad p hp).1 ho
      rw [(hrad p hp).2] at hq
      exact ⟨q,fun _ => ⟨hq,hpos⟩⟩
    · exact ⟨p,fun hh => False.elim (hp hh)⟩
  choose tip htip using htipchoice
  refine ⟨radial,tip,(fun p hp => (hrad p hp).1),?_,(fun p hp => (htip p hp).1),
    (fun p hp => (htip p hp).2)⟩
  intro p hp
  have h := intersection_on_right _ _ (noParallel_any n L hL line (radial p)
    line.isLt (radial p).isLt (fun h => (hrad p hp).1 (Fin.ext h).symm))
  simpa only [(hrad p hp).2] using h

#print axioms not_concurrent_of_triples
#print axioms common_positive_cut_ordinary
#print axioms ordinary_endpoint_selectors
#print axioms triple_ordinary_crossing_identity
#print axioms triple_even_ordinary_crossings_odd
#print axioms triple_even_no_ordinary_pair_partition
#print axioms ordinary_crossings_common_side
end Kobon.UpperOpenMathOrdinaryCutParity

