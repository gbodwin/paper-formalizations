import OnlineReachabilityPreservers.FullThreeHexGrid
import OnlineReachabilityPreservers.HalfGridCleaning
import OnlineReachabilityPreservers.LiteralFrozenFullLowMass

/-! A full-three witness for the literal half benchmark at large vertex budgets. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- At a mean degree above eight, the half-three moment forces a large path square. -/
theorem half_three_dense_mass_requires_path_square {n p k : ℕ} (hn : 0 < n) (three : 3 ≤ k)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k)
    (dense : 8*n < ∑ i, (paths i).length) : 40*n < p*p := by
  let M := ∑ i, (paths i).length
  have h₀ : 8*n < M := dense
  have moment : M^2 ≤ n*(p*p+3*M) :=
    (listMass_square_le_halfThree_degree paths simple free three).trans
      (Nat.mul_le_mul_left _ (by omega))
  have sq := Nat.mul_lt_mul_of_pos_right h₀ (show 0 < M by omega)
  have above := Nat.mul_lt_mul_of_pos_left h₀ (show 0 < 5*n by positivity)
  apply (Nat.mul_lt_mul_left hn).mp
  nlinarith only [moment,sq,above]

private theorem hex_grid_frozen_dimensions {n p M : ℕ} (hp : 0 < p) (unbalanced : 8*p ≤ n)
    (dense : 8*n < M) (upper : M ≤ 12*n) (pairs : 40*n < p*p) :
    ∃ w : ℕ, 2 ≤ w ∧ (2*w-1)^2 ≤ n ∧ 3*(2*w-1) ≤ p ∧ M ≤ (4*p)*w ∧ p*(2*w-1) ≤ 4*M := by
  let w := (M+4*p-1)/(4*p)
  have hM : 0 < M := by omega
  obtain ⟨wPos,lower,above⟩ := quarterMean_ceiling hp hM
  change 0 < w at wPos
  change M ≤ (4*p)*w at lower
  change (4*p)*w ≤ M+4*p-1 at above
  have wBig : 2 ≤ w := by
    by_contra! small
    have cap := Nat.mul_le_mul_left (4*p) (show w ≤ 1 by omega)
    omega
  have cubic : 8*(p*w) ≤ 25*n := by
    rw [Nat.mul_assoc] at above
    omega
  have squared := Nat.pow_le_pow_left cubic 2
  have product := Nat.mul_le_mul_left n pairs.le
  have bounded : (64*(4*w^2))*p^2 ≤ (64*n)*p^2 := by
    nlinarith only [squared,product,Nat.zero_le (n^2)]
  have squareFit : 4*w^2 ≤ n := by
    have inner := Nat.le_of_mul_le_mul_right bounded (show 0 < p^2 by positivity)
    omega
  have vertexFit : (2*w-1)^2 ≤ n := calc
    _ ≤ (2*w)^2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
    _ = 4*w^2 := by ring
    _ ≤ _ := squareFit
  have six : 6*w ≤ p := by
    have raw : (8*p)*(6*w) ≤ (8*p)*p := by nlinarith only [cubic,pairs,Nat.zero_le n]
    exact Nat.le_of_mul_le_mul_left raw (show 0 < 8*p by positivity)
  have pathFit : 3*(2*w-1) ≤ p := by
    have fit := Nat.mul_le_mul_left 3 (Nat.sub_le (2*w) 1)
    omega
  have high : p*(2*w-1) ≤ 4*M := by
    have fit := Nat.mul_le_mul_left p (Nat.sub_le (2*w) 1)
    have cutting : (4*p)*w ≤ M+4*p := above.trans (Nat.sub_le _ _)
    nlinarith only [fit,cutting,show p ≤ M by omega]
  exact ⟨w,wBig,vertexFit,pathFit,lower,high⟩

set_option maxHeartbeats 900000 in
/-- Disjoint copies of a finite full-three-free family with uniform degree and
bounded lengths meet the original caps when one copy fits and the four mass inequalities hold. -/
theorem frozen_cleaning_full_three_of_regular_copies {V I : Type*} [LinearOrder V] [Fintype V]
    [LinearOrder I] [Fintype I] {n p M d w width : ℕ} (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) 3)
    (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card = d)
    (lens : ∀ i, w ≤ (paths i).length ∧ (paths i).length ≤ width) (long : 2 ≤ w)
    (hasRows : 0 < Fintype.card I) (vertexFit : Fintype.card V ≤ n) (pathFit : Fintype.card I ≤ p)
    (massLow : d*n ≤ M) (massHigh : M ≤ (4*d)*n) (lowLen : M ≤ (4*p)*w) (highLen : p*width ≤ 4*M) :
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
      M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let N := Fintype.card V
  let P := Fintype.card I
  have mass : (∑ i, (paths i).length) = d*N := calc
    _ = ∑ i, (paths i).toFinset.card := sum_congr rfl (fun i _ => (List.toFinset_card_of_nodup (simple i)).symm)
    _ = ∑ v, (occurrences (fun i => (paths i).toFinset) v).card := (sum_occurrences _).symm
    _ = _ := by simp [degree,N,Nat.mul_comm]
  have lengths : P*w ≤ d*N := calc
    _ = ∑ _ : I, w := by simp [P]
    _ ≤ ∑ i, (paths i).length := sum_le_sum fun i _ => (lens i).1
    _ = _ := mass
  have hasVertices : 0 < N := by
    have positive : 0 < P*w := Nat.mul_pos hasRows (by omega)
    by_contra! empty
    have zero : N = 0 := by omega
    rw [zero,mul_zero] at lengths
    omega
  let copies := min (n/N) (p/P)
  have vFit : copies*N ≤ n := (Nat.mul_le_mul_right _ (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
  have pFit : copies*P ≤ p := (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  let input (_ : Fin copies) := paths
  let family := disjointListFamilies input
  have familySimple : ∀ i, (family i).Nodup := disjointListFamilies_simple input (fun _ => simple)
  have legal : localOrderAdmissible false 3 family :=
    disjointListFamilies_admissible input (fun _ => simple) (fun _ => free)
  let rows := relabelListPathsFin family
  obtain ⟨rowSimple,rowFree,exactMass,rowDegree,rowLength⟩ := relabelListPathsFin_spec family familySimple legal
  let usedV := Fintype.card (V ×ₗ Fin copies)
  let usedP := Fintype.card (I ×ₗ Fin copies)
  have vCount : usedV = copies*N := by
    unfold usedV N
    rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]
  have rCount : usedP = copies*P := by
    unfold usedP P
    rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]
  have familyMass : (∑ i, (family i).length) = copies*(d*N) := by
    rw [show family = disjointListFamilies input from rfl,disjointListFamilies_mass]
    simp [input,mass,Nat.mul_assoc,Nat.mul_comm]
  have rowMass : (∑ i, (rows i).length) = copies*(d*N) := exactMass.trans familyMass
  have enough : M ≤ 8*(copies*(d*N)) := by
    by_cases vertexWins : n/N ≤ p/P
    · have paid := floorBlockMass hasVertices vertexFit
      rw [← show copies = n/N from min_eq_left vertexWins] at paid
      calc
        _ ≤ (4*d)*n := massHigh
        _ ≤ (4*d)*(2*(copies*N)) := Nat.mul_le_mul_left (4*d) paid
        _ = _ := by ring
    · have paid := floorBlockMass hasRows pathFit
      rw [← show copies = p/P from min_eq_right (le_of_not_ge vertexWins)] at paid
      calc
        _ ≤ (4*p)*w := lowLen
        _ ≤ 8*(copies*(P*w)) := by
          convert Nat.mul_le_mul_right (4*w) paid using 1 <;> ring
        _ ≤ 8*(copies*(d*N)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ lengths)
  have noExcess : copies*(d*N) ≤ M := calc
    _ = d*(copies*N) := by ring
    _ ≤ d*n := Nat.mul_le_mul_left _ vFit
    _ ≤ _ := massLow
  have full : BridgeFree (Before rows) 3 := rowFree
  have widths (i : Fin usedP) : w ≤ (rows i).length ∧ (rows i).length ≤ width := by
    rw [rowLength]
    simpa only [family,disjointListFamilies,List.length_map,input] using
      lens (ofLex (Fintype.orderIsoFinOfCardEq (I ×ₗ Fin copies) rfl i)).1
  have rowLong (i : Fin usedP) : 2 ≤ (rows i).length := long.trans (widths i).1
  have unique := nontrivial_halfFree_paths_injective rowSimple rowLong (by decide : 2 ≤ 3) full.halfFree
  have hn : 0 < n := hasVertices.trans_le vertexFit
  have hp : 0 < p := hasRows.trans_le pathFit
  refine ⟨usedV,vCount.trans_le vFit,usedP,rCount.trans_le pFit,rows,unique,?_,full,?_,?_,?_⟩
  · intro i
    exact ⟨List.length_pos_iff.mp (lt_of_lt_of_le (by decide) (rowLong i)),rowSimple i⟩
  · rwa [rowMass]
  · rwa [rowMass]
  · constructor
    · intro v
      rw [rowDegree,(disjointListFamilies_degree input _).trans (degree _)]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
        exact_mod_cast (show M ≤ d*(4*n) by simpa only [Nat.mul_assoc,Nat.mul_comm 4 d] using massHigh)
      · apply (le_div_iff₀ (by positivity : (0:ℝ) < n)).mpr
        have cap : d*n ≤ 4*M := massLow.trans (by omega)
        exact_mod_cast cap
    · intro i
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).mpr
        have cap := lowLen.trans (Nat.mul_le_mul_left (4*p) (widths i).1)
        rw [Nat.mul_comm (4*p)] at cap
        exact_mod_cast cap
      · apply (le_div_iff₀ (by positivity : (0:ℝ) < p)).mpr
        have cap := (Nat.mul_le_mul_left p (widths i).2).trans highLen
        exact_mod_cast (show (rows i).length*p ≤ 4*M by simpa [Nat.mul_comm] using cap)


/-- Disjoint copies of the full-three hexagonal grid meet the four
starting caps when the mass is between eight and twelve times the
vertex budget and the path budget meets the indicated square bound. -/
theorem frozen_cleaning_full_three_hex_grid {n p M : ℕ} (hp : 0 < p) (unbalanced : 8*p ≤ n)
    (dense : 8*n < M) (upper : M ≤ 12*n) (pairs : 40*n < p*p) :
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
      M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨w,long,vertexFits,pathFits,lowLen,highLen⟩ := hex_grid_frozen_dimensions hp unbalanced dense upper pairs
  have hasRows : 0 < Fintype.card (HexGridPath w) := by rw [hexGridRows_card_paths]; omega
  exact frozen_cleaning_full_three_of_regular_copies (hexGridRows w) hexGridRows_simple (hexGridRows_full_three w)
    hexGridRows_degree hexGridRows_length long hasRows ((hexGridRows_card_vertices w).trans vertexFits)
    ((hexGridRows_card_paths w).trans_le pathFits) (by omega) (by omega) lowLen highLen

/-- At cutoff three, a feasible literal half maximum has a full-free
witness with both budgets and all four starting caps in this range. -/
theorem localOrderDistinctExtremal_frozen_full_three_of_large_vertex_budget {n p : ℕ}
    (hp : 0 < p) (unbalanced : 8*p ≤ n) (budget : p*p-p ≤ 108*n)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
          (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        M ≤ 8*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨paths,distinct,well,half,maximal,dense,long⟩ := localOrderDistinctExtremal_isDense (k := 3) true hp feasible
  refine ⟨paths,distinct,well,half,maximal,?_⟩
  let M := ∑ i, (paths i).length
  have hn : 0 < n := by omega
  by_cases low : M ≤ 8*n
  · have upper : M ≤ 8*max n p := low.trans (Nat.mul_le_mul_left _ (le_max_left _ _))
    obtain ⟨v,vFit,q,qFit,rows,unique,valid,free,retained,cap,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct well half (by decide) hn hp dense upper
    exact ⟨v,vFit,q,qFit,rows,unique,valid,free 3,retained,cap,caps⟩
  have simple (i : Fin p) := (well i).2
  have moment : M^2 ≤ n*(p*p-p+3*M) := listMass_square_le_halfThree_degree paths simple half le_rfl
  have upper : M ≤ 12*n := mass_le_mul_of_quadratic hn (a := 12) (c := 9) (by decide)
    (moment.trans (Nat.mul_le_mul_left n (by omega)))
  have many := half_three_dense_mass_requires_path_square hn le_rfl paths simple half (lt_of_not_ge low)
  exact frozen_cleaning_full_three_hex_grid hp unbalanced (lt_of_not_ge low) upper many

end OnlineReachabilityPreservers
