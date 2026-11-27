import OnlineReachabilityPreservers.PositiveMatchingHalfRows
import OnlineReachabilityPreservers.LocalRegularization

/-! Quadratic shift certificates for many positive matching fibers. -/

namespace OnlineReachabilityPreservers

open Finset Sum3
open SimpleGraph.TripartiteFromTriangles
local notation "Before" => SourceAudit.BeforeIn

private abbrev ShiftVector (d N : ℕ) := Fin d → Fin N
private abbrev ShiftStart (d N : ℕ) := ShiftVector d N × Fin (d*N^2)
private abbrev ShiftTarget (d N : ℕ) := ShiftVector d (2*N) × Fin (2*d*N^2)

private def shiftNorm {d N : ℕ} (a : ShiftVector d N) : ℕ :=
  ∑ i, (a i).val^2

private theorem shiftNorm_le {d N : ℕ} (a : ShiftVector d N) : shiftNorm a ≤ d*N^2 := calc
  _ ≤ ∑ _ : Fin d, N^2 := sum_le_sum (fun i _ => Nat.pow_le_pow_left (a i).isLt.le _)
  _ = _ := by simp

private def shiftEndpoint {d N : ℕ} (x : ShiftStart d N) (a : ShiftVector d N) : ShiftTarget d N :=
  (fun i => ⟨(x.1 i).val+(a i).val,by have := (x.1 i).isLt; have := (a i).isLt; omega⟩,
    ⟨x.2.val+shiftNorm a,by
      have before := x.2.isLt
      have width := shiftNorm_le a
      have total : 2*d*N^2 = 2*(d*N^2) := by ring
      omega⟩)

private theorem shiftEndpoint_inj_start {d N : ℕ} {a : ShiftVector d N} {x y : ShiftStart d N}
    (same : shiftEndpoint x a = shiftEndpoint y a) : x = y := by
  apply Prod.ext
  · funext i
    apply Fin.ext
    have coordinate := congrArg (fun p : ShiftTarget d N => (p.1 i).val) same
    exact Nat.add_right_cancel coordinate
  · apply Fin.ext
    have height := congrArg (fun p : ShiftTarget d N => p.2.val) same
    exact Nat.add_right_cancel height

private theorem shiftEndpoint_inj_vector {d N : ℕ} {x : ShiftStart d N} {a b : ShiftVector d N}
    (same : shiftEndpoint x a = shiftEndpoint x b) : a = b := by
  funext i
  apply Fin.ext
  have coordinate := congrArg (fun p : ShiftTarget d N => (p.1 i).val) same
  exact Nat.add_left_cancel coordinate

private def shiftTriples (d N : ℕ) : Finset (ShiftStart d N × ShiftTarget d N × ShiftVector d N) :=
  univ.image (fun p : ShiftStart d N × ShiftVector d N => (p.1,shiftEndpoint p.1 p.2,p.2))

private theorem mem_shiftTriples {d N : ℕ} {x : ShiftStart d N} {y : ShiftTarget d N} {a : ShiftVector d N} :
    (x,y,a) ∈ shiftTriples d N ↔ shiftEndpoint x a = y := by
  unfold shiftTriples
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨⟨u,b⟩,equal⟩
    have xu : u = x := congrArg Prod.fst equal
    have ba : b = a := congrArg (fun p : ShiftStart d N × ShiftTarget d N × ShiftVector d N => p.2.2) equal
    have target : shiftEndpoint u b = y :=
      congrArg (fun p : ShiftStart d N × ShiftTarget d N × ShiftVector d N => p.2.1) equal
    rwa [xu,ba] at target
  · intro endpoint
    exact ⟨(x,a),Prod.ext rfl (Prod.ext endpoint rfl)⟩

private theorem shiftTriples_disjoint (d N : ℕ) : ExplicitDisjoint (shiftTriples d N) where
  inj₀ := fun {_ _ _ _} first next =>
    shiftEndpoint_inj_start ((mem_shiftTriples.mp first).trans (mem_shiftTriples.mp next).symm)
  inj₁ := fun {_ _ _ _} first next => (mem_shiftTriples.mp first).symm.trans (mem_shiftTriples.mp next)
  inj₂ := fun {_ _ _ _} first next =>
    shiftEndpoint_inj_vector ((mem_shiftTriples.mp first).trans (mem_shiftTriples.mp next).symm)

private theorem shiftTriples_card (d N : ℕ) :
    (shiftTriples d N).card = Fintype.card (ShiftStart d N)*Fintype.card (ShiftVector d N) := by
  unfold shiftTriples
  rw [card_image_of_injective,card_univ,Fintype.card_prod]
  intro a b same
  exact Prod.ext (congrArg (fun p : ShiftStart d N × ShiftTarget d N × ShiftVector d N => p.1) same)
    (congrArg (fun p : ShiftStart d N × ShiftTarget d N × ShiftVector d N => p.2.2) same)

private theorem shiftTriples_fiber_card {d N : ℕ} (a : ShiftVector d N) :
    ((shiftTriples d N).filter (fun t => t.2.2 = a)).card = Fintype.card (ShiftStart d N) := by
  let triangle (x : ShiftStart d N) := (x,shiftEndpoint x a,a)
  have same : (shiftTriples d N).filter (fun t => t.2.2 = a) = univ.image triangle := by
    ext ⟨x,y,b⟩
    rw [mem_filter,mem_shiftTriples,mem_image]
    constructor
    · rintro ⟨hit,rfl⟩
      exact ⟨x,mem_univ _,Prod.ext rfl (Prod.ext hit rfl)⟩
    · rintro ⟨u,_,equal⟩
      have starts : u = x := congrArg Prod.fst equal
      have ends : shiftEndpoint u a = y :=
        congrArg (fun p : ShiftStart d N × ShiftTarget d N × ShiftVector d N => p.2.1) equal
      have shifts : a = b :=
        congrArg (fun p : ShiftStart d N × ShiftTarget d N × ShiftVector d N => p.2.2) equal
      rw [← starts,← shifts]
      exact ⟨ends,rfl⟩
  rw [same,card_image_of_injective _ (fun _ _ same =>
    congrArg (fun p : ShiftStart d N × ShiftTarget d N × ShiftVector d N => p.1) same),card_univ]

private def shiftLeftWeight {d N : ℕ} (a : ShiftVector d N) (x : ShiftStart d N) : ℝ :=
  2*x.2.val-4*(∑ i, ((a i).val:ℝ)*(x.1 i).val)

private def shiftRightWeight {d N : ℕ} (a : ShiftVector d N) (y : ShiftTarget d N) : ℝ :=
  -2*y.2.val+4*(∑ i, ((a i).val:ℝ)*(y.1 i).val)-2*shiftNorm a+1

private theorem shiftWeight_sum {d N : ℕ} (a b : ShiftVector d N) (x : ShiftStart d N) :
    shiftLeftWeight a x+shiftRightWeight a (shiftEndpoint x b) =
      1-2*(∑ i, (((b i).val:ℝ)-(a i).val)^2) := by
  have height : ((shiftEndpoint x b).2.val:ℝ) = (x.2.val:ℝ)+shiftNorm b := by
    change ((x.2.val+shiftNorm b:ℕ):ℝ) = _
    exact Nat.cast_add _ _
  have dot : (∑ i, ((a i).val:ℝ)*((shiftEndpoint x b).1 i).val) =
      (∑ i, ((a i).val:ℝ)*(x.1 i).val)+(∑ i, ((a i).val:ℝ)*(b i).val) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    change ((a i).val:ℝ)*(((x.1 i).val+(b i).val:ℕ):ℝ) = _
    rw [Nat.cast_add]
    ring
  have norm (s : ShiftVector d N) : ((shiftNorm s):ℝ) = ∑ i, ((s i).val:ℝ)^2 := by
    simp [shiftNorm,Nat.cast_sum]
  have energy : (∑ i, (((b i).val:ℝ)-(a i).val)^2) =
      (∑ i, ((b i).val:ℝ)^2)+(∑ i, ((a i).val:ℝ)^2)-2*(∑ i, ((a i).val:ℝ)*(b i).val) := by
    rw [mul_sum,← sum_add_distrib,← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [shiftLeftWeight,shiftRightWeight,height,dot,norm,norm,energy]
  ring

private theorem cast_difference_square_ge_one {u v : ℕ} (apart : u ≠ v) :
    (1:ℝ) ≤ ((u:ℝ)-v)^2 := by
  rcases lt_or_gt_of_ne apart with low | high
  · have separation : (u:ℝ)+1 ≤ v := by exact_mod_cast Nat.succ_le_of_lt low
    have first : 0 ≤ (v:ℝ)-u-1 := by linarith
    have next : 0 ≤ (v:ℝ)-u+1 := by linarith
    nlinarith only [mul_nonneg first next]
  · have separation : (v:ℝ)+1 ≤ u := by exact_mod_cast Nat.succ_le_of_lt high
    have first : 0 ≤ (u:ℝ)-v-1 := by linarith
    have next : 0 ≤ (u:ℝ)-v+1 := by linarith
    nlinarith only [mul_nonneg first next]

private theorem shiftWeight_positive {d N : ℕ} (a b : ShiftVector d N) (x : ShiftStart d N) :
    0 < shiftLeftWeight a x+shiftRightWeight a (shiftEndpoint x b) ↔ a = b := by
  rw [shiftWeight_sum]
  constructor
  · intro positive
    by_contra mismatch
    have missing : ¬ ∀ i, b i = a i := fun same => mismatch (funext same).symm
    obtain ⟨i,apart⟩ := not_forall.mp missing
    have separated : (b i).val ≠ (a i).val := fun same => apart (Fin.ext same)
    have positiveTerm := cast_difference_square_ge_one separated
    have dominate : (((b i).val:ℝ)-(a i).val)^2 ≤ ∑ j, (((b j).val:ℝ)-(a j).val)^2 :=
      single_le_sum (f := fun j => (((b j).val:ℝ)-(a j).val)^2) (fun j _ => sq_nonneg _) (mem_univ i)
    linarith
  · rintro rfl
    simp

private theorem shiftTriples_positive {d N : ℕ} (x : ShiftStart d N) (y : ShiftTarget d N) (a : ShiftVector d N)
    (edge : ∃ b, (x,y,b) ∈ shiftTriples d N) :
    0 < shiftLeftWeight a x+shiftRightWeight a y ↔ (x,y,a) ∈ shiftTriples d N := by
  obtain ⟨b,hit⟩ := edge
  have same := mem_shiftTriples.mp hit
  rw [← same,shiftWeight_positive,mem_shiftTriples]
  exact ⟨congrArg (shiftEndpoint x),shiftEndpoint_inj_vector⟩

private theorem shiftVector_card (d N : ℕ) : Fintype.card (ShiftVector d N) = N^d := by
  change Fintype.card (Fin d → Fin N) = _
  simp

private theorem shiftStart_card (d N : ℕ) : Fintype.card (ShiftStart d N) = N^d*(d*N^2) := by
  change Fintype.card (ShiftVector d N × Fin (d*N^2)) = _
  rw [Fintype.card_prod,shiftVector_card,Fintype.card_fin]

private theorem shiftTarget_card (d N : ℕ) : Fintype.card (ShiftTarget d N) = (2*N)^d*(2*d*N^2) := by
  change Fintype.card (ShiftVector d (2*N) × Fin (2*d*N^2)) = _
  rw [Fintype.card_prod,shiftVector_card,Fintype.card_fin]

/-- A finite-box version of the quadratic shift construction for
positive matchings. Every shift has the same complete inner source box,
and the outer target box accommodates all shifts. Distinct fibers have
disjoint edges. -/
theorem quadratic_shift_positive_matching_boxes (d N : ℕ) :
    let A := Fin d → Fin N
    let L := A × Fin (d*N^2)
    let R := (Fin d → Fin (2*N)) × Fin (2*d*N^2)
    ∃ t : Finset (L × R × A),
      ExplicitDisjoint t ∧ t.card = N^d*(d*N^2)*N^d ∧
      (∀ a : A, (t.filter fun e => e.2.2 = a).card = N^d*(d*N^2)) ∧
      ∃ (left : A → L → ℝ) (right : A → R → ℝ),
        ∀ x y a, (∃ b, (x,y,b) ∈ t) → (0 < left a x+right a y ↔ (x,y,a) ∈ t) := by
  refine ⟨shiftTriples d N,shiftTriples_disjoint d N,?_,?_,shiftLeftWeight,shiftRightWeight,
    shiftTriples_positive⟩
  · rw [shiftTriples_card,shiftStart_card,shiftVector_card]
  · intro a
    rw [shiftTriples_fiber_card,shiftStart_card]

/-- Quadratic shift fibers give many distinct length-three rows with
last-arc half exclusion through every cutoff, at the stated exact
vertex and path counts. -/
theorem quadratic_shift_half_rows (d N : ℕ) :
    let n := N^d*(d*N^2)+((2*N)^d*(2*d*N^2)+N^d)
    let p := N^d*(d*N^2)*N^d
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, (rows i).Nodup ∧ (rows i).length = 3) ∧
      (∀ cutoff, HalfBridgeFree (Before rows) cutoff) ∧ (∑ i, (rows i).length) = 3*p := by
  classical
  let n := N^d*(d*N^2)+((2*N)^d*(2*d*N^2)+N^d)
  let p := N^d*(d*N^2)*N^d
  let V := ShiftStart d N ⊕ ShiftTarget d N ⊕ ShiftVector d N
  obtain ⟨t,disjoint,pathCard,_,left,right,positive⟩ := quadratic_shift_positive_matching_boxes d N
  let : ExplicitDisjoint t := disjoint
  obtain ⟨arrival,injective,profile,free⟩ := exists_halfFree_three_rows_of_positive_matchings t left right positive
  have card : Fintype.card V = n := by
    change Fintype.card (ShiftStart d N ⊕ (ShiftTarget d N ⊕ ShiftVector d N)) = _
    rw [Fintype.card_sum,Fintype.card_sum,shiftStart_card,shiftTarget_card,shiftVector_card]
  let vertex := Fintype.equivFinOfCardEq card
  let original (i : Fin t.card) := tripartiteThreeRow (arrival i)
  let rows (i : Fin t.card) := (original i).map vertex
  have undo (i : Fin t.card) : (rows i).map vertex.symm = original i := by simp [rows,List.map_map]
  have lengths (i : Fin t.card) : (rows i).length = 3 := by
    simpa only [rows,List.length_map,original] using (profile i).2
  have stillFree (cutoff : ℕ) : HalfBridgeFree (Before rows) cutoff := by
    intro k size bridge earlier
    exact free cutoff size (bridge.mapVertices vertex.symm vertex.symm.injective (fun i _ _ step => by
      simpa only [SourceAudit.BeforeIn,undo] using
        listBefore_map vertex.symm ((undo i).symm ▸ (profile i).1) step)) earlier
  let Output (r : ℕ) : Prop := ∃ rows : Fin r → List (Fin n), Function.Injective rows ∧
    (∀ i, (rows i).Nodup ∧ (rows i).length = 3) ∧
    (∀ cutoff, HalfBridgeFree (Before rows) cutoff) ∧ (∑ i, (rows i).length) = 3*r
  have witness : Output t.card := ⟨rows,(List.map_injective_iff.mpr vertex.injective).comp injective,
    fun i => ⟨(profile i).1.map vertex.injective,lengths i⟩,stillFree,by simp [lengths,Nat.mul_comm]⟩
  exact pathCard ▸ witness

/-- The mass of the length-three construction grows at least as the
vertex count to the power `2-2/(d+2)`, up to a factor depending on
`d`. The inequality is written with integer powers. -/
theorem quadratic_shift_mass_power_lower_bound (d N : ℕ) (positiveD : 0 < d) (positiveN : 0 < N) :
    let n := N^d*(d*N^2)+((2*N)^d*(2*d*N^2)+N^d)
    let mass := 3*(N^d*(d*N^2)*N^d)
    n^(2*d+2) ≤ (d+2^(d+1)*d+1)^(2*d+2)*mass^(d+2) := by
  let n := N^d*(d*N^2)+((2*N)^d*(2*d*N^2)+N^d)
  let W := 3*(N^d*(d*N^2)*N^d)
  let C := d+2^(d+1)*d+1
  have vertexFormula : n = (d+2^(d+1)*d)*N^(d+2)+N^d := by
    simp only [n,mul_pow,pow_add,pow_one]
    ring
  have nLe : n ≤ C*N^(d+2) := calc
    _ = (d+2^(d+1)*d)*N^(d+2)+N^d := vertexFormula
    _ ≤ (d+2^(d+1)*d)*N^(d+2)+N^(d+2) :=
      Nat.add_le_add_left (Nat.pow_le_pow_right positiveN (by omega)) _
    _ = _ := by dsimp only [C]; ring
  have weighted : W = (3*d)*N^(2*d+2) := by
    simp only [W,two_mul,pow_add]
    ring
  have massLe : N^(2*d+2) ≤ W := calc
    _ ≤ (3*d)*N^(2*d+2) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := weighted.symm
  calc
    n^(2*d+2) ≤ (C*N^(d+2))^(2*d+2) := Nat.pow_le_pow_left nLe _
    _ = C^(2*d+2)*(N^(2*d+2))^(d+2) := by
      rw [mul_pow,← pow_mul,← pow_mul,Nat.mul_comm (d+2) (2*d+2)]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left massLe _)

end OnlineReachabilityPreservers
