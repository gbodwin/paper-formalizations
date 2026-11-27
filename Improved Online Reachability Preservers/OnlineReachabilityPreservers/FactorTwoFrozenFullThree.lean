import OnlineReachabilityPreservers.WengerThreeRows
import OnlineReachabilityPreservers.ExtremalCopyBounds
import OnlineReachabilityPreservers.FullDisjointUnion
import OnlineReachabilityPreservers.FullThreeLiteralFeasibility

/-! A full-three starting-average witness for budgets within a factor two. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- At ratio at most two, the latest-common-vertex estimate controls the
half mass using a width chosen against the larger budget. -/
theorem half_three_mass_scaled_le_min_of_ratio_two {n p width cutoff : ℕ}
    (hn : 0 < n) (hp : 0 < p) (ratio : max n p ≤ 2*min n p)
    (large : 4096 ≤ width) (scale : 16*max n p ≤ 73*width^3)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) :
    16*(∑ i, (paths i).length) ≤ 63*(min n p * width) := by
  let a := max n p
  let b := min n p
  let M := ∑ i, (paths i).length
  let S := M-M/64-(64*n+p)
  have cube : S^3 ≤ 6*(n*p)^2 :=
    half_three_latest_intersection_shifted_mass_cube_le hn hp paths simple half three 63
  have na : n ≤ a := le_max_left _ _
  have pa : p ≤ a := le_max_right _ _
  have charge : 64*n+p ≤ 130*b := by change a ≤ 2*b at ratio; omega
  have smallCharge : 16*(64*n+p) ≤ b*width := calc
    _ ≤ 2080*b := by omega
    _ ≤ width*b := Nat.mul_le_mul_right _ (by omega)
    _ = _ := Nat.mul_comm _ _
  have exactProduct : n*p = a*b := by
    rcases le_total n p with h | h
    · simp [a,b,max_eq_right h,min_eq_left h,Nat.mul_comm]
    · simp [a,b,max_eq_left h,min_eq_right h]
  have volume : 16*(n*p)^2 ≤ 146*(b*width)^3 := calc
    _ = (16*a)*(a*b^2) := by rw [exactProduct]; ring
    _ ≤ (73*width^3)*((2*b)*b^2) := Nat.mul_le_mul scale (Nat.mul_le_mul_right _ ratio)
    _ = _ := by ring
  by_contra! excess
  change 63*(b*width) < 16*M at excess
  have floor : 64*(M/64) ≤ M := Nat.mul_div_le _ _
  have gap : 61*(b*width) < 16*S := by dsimp only [S]; omega
  have cap : 16*(16*S)^3 ≤ 16*(61*(b*width))^3 := calc
    _ = 16^3*(16*S^3) := by ring
    _ ≤ (16^3*6)*(16*(n*p)^2) := by
      convert Nat.mul_le_mul_left (16^3) (Nat.mul_le_mul_left 16 cube) using 1
      ring
    _ ≤ (16^3*6)*(146*(b*width)^3) := Nat.mul_le_mul_left _ volume
    _ = (16^3*6*146)*(b*width)^3 := by ring
    _ ≤ (16*61^3)*(b*width)^3 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring
  exact (not_lt_of_ge cap) (Nat.mul_lt_mul_of_pos_left
    (pow_lt_pow_left₀ gap (Nat.zero_le _) (by decide : 3 ≠ 0)) (by decide))

private theorem exists_dyadic_slope_scale {a : ℕ} (large : 8192^3 ≤ a) :
    ∃ m slopes : ℕ, 0 < m ∧ 4096 ≤ slopes ∧ slopes ≤ 2^m ∧
      slopes*(2^m)^2 ≤ a ∧ a ≤ 4*(slopes*(2^m)^2) ∧
      4*a ≤ 15*(2^m)^3 ∧ 16*a ≤ 73*slopes^3 := by
  let m := Nat.log 8 a
  let q := 2^m
  have aPos : 0 < a := Nat.lt_of_lt_of_le (by decide) large
  have size : 13 ≤ m := Nat.le_log_of_pow_le (by decide) (by exact large)
  have qLarge : 8192 ≤ q := Nat.pow_le_pow_right (by decide : 0 < 2) size
  have power : q^3 = 8^m := by dsimp only [q]; rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have lower : q^3 ≤ a := power.trans_le (Nat.pow_log_le_self 8 aPos.ne')
  have upper : a < 8*q^3 := calc
    _ < 8^(m+1) := Nat.lt_pow_succ_log_self (by decide : 1 < 8) a
    _ = _ := by rw [power,pow_succ,Nat.mul_comm]
  by_cases small : 4*a ≤ 15*q^3
  · have cube : q*q^2 = q^3 := by ring
    refine ⟨m,q,by omega,by omega,le_rfl,?_,?_,small,by omega⟩
    · change q*q^2 ≤ a
      rwa [cube]
    · change a ≤ 4*(q*q^2)
      rw [cube]
      omega
  · let r := 2*q
    let slopes := a/r^2
    have rEq : 2^(m+1) = r := by simp [r,q,pow_succ,Nat.mul_comm]
    have qPos : 0 < q := by omega
    have squarePos : 0 < r^2 := by dsimp only [r]; positivity
    have rCube : r^3 = 8*q^3 := by dsimp only [r]; ring
    have aSmall : a ≤ r^3 := upper.le.trans_eq rCube.symm
    have slopesLarge : 4096 ≤ slopes := (Nat.le_div_iff_mul_le squarePos).mpr (by
      calc
        _ = 16384*q^2 := by dsimp only [r]; ring
        _ ≤ (2*q)*q^2 := Nat.mul_le_mul_right _ (by omega)
        _ = 2*q^3 := by ring
        _ ≤ _ := by omega)
    have fit : slopes*r^2 ≤ a := Nat.div_mul_le_self _ _
    have last : a < (slopes+1)*r^2 := by
      simpa only [slopes,Nat.mul_comm] using Nat.lt_mul_div_succ a squarePos
    have slopesFit : slopes ≤ r := by
      apply Nat.le_of_mul_le_mul_right _ squarePos
      exact fit.trans (by convert aSmall using 1; ring)
    have envelope : a ≤ 4*(slopes*r^2) := calc
      _ ≤ (slopes+1)*r^2 := last.le
      _ ≤ (4*slopes)*r^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
    have ratio : 15*q ≤ 16*(slopes+1) := by
      apply Nat.le_of_mul_le_mul_right (c := q^2) _ (by positivity)
      calc
        _ = 15*q^3 := by ring
        _ ≤ 4*a := by omega
        _ ≤ 4*((slopes+1)*r^2) := Nat.mul_le_mul_left _ last.le
        _ = _ := by dsimp only [r]; ring
    have square : 225*q^2 ≤ 256*(slopes+1)^2 := calc
      _ = (15*q)^2 := by ring
      _ ≤ (16*(slopes+1))^2 := Nat.pow_le_pow_left ratio 2
      _ = _ := by ring
    have rough : 225*(16*a) ≤ 16384*(slopes+1)^3 := calc
      _ ≤ 225*(16*((slopes+1)*r^2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ last.le)
      _ = (64*(slopes+1))*(225*q^2) := by dsimp only [r]; ring
      _ ≤ (64*(slopes+1))*(256*(slopes+1)^2) := Nat.mul_le_mul_left _ square
      _ = _ := by ring
    have rounded : 2048^3*(225*(16*a)) ≤ 2048^3*(225*(73*slopes^3)) := calc
      _ ≤ 2048^3*(16384*(slopes+1)^3) := Nat.mul_le_mul_left _ rough
      _ = 16384*(2048*(slopes+1))^3 := by ring
      _ ≤ 16384*(2049*slopes)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      _ = (16384*2049^3)*slopes^3 := by ring
      _ ≤ (2048^3*225*73)*slopes^3 := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring
    have volume : 16*a ≤ 73*slopes^3 := Nat.le_of_mul_le_mul_left
      (Nat.le_of_mul_le_mul_left rounded (by decide : 0 < (2048:ℕ)^3)) (by decide : 0 < 225)
    exact ⟨m+1,slopes,by omega,slopesLarge,by rw [rEq]; exact slopesFit,
      by rw [rEq]; exact fit,by rw [rEq]; exact envelope,by rw [rEq]; omega,volume⟩

private theorem exists_layer_width_with_reserve {a b q slopes : ℕ}
    (ordered : b ≤ a) (ratio : a ≤ 2*b) (large : 4096 ≤ slopes) (slopeFit : slopes ≤ q)
    (budget : slopes*q^2 ≤ a) (envelope : 4*a ≤ 15*q^3) :
    ∃ layers : ℕ, 2 ≤ layers ∧ layers ≤ q ∧ (layers+1)*q^2 ≤ b ∧
      b ≤ 4*(layers*q^2) ∧ b*slopes ≤ a*layers+2*a := by
  let available := min q (b/q^2)
  let layers := available-1
  have qLarge : 4096 ≤ q := large.trans slopeFit
  have squarePos : 0 < q^2 := by positivity
  have enough : 6*q^2 ≤ a := (Nat.mul_le_mul_right _ (by omega : 6 ≤ slopes)).trans budget
  have availableLarge : 3 ≤ available := le_min (by omega)
    ((Nat.le_div_iff_mul_le squarePos).mpr (by omega))
  have layerLarge : 2 ≤ layers := by dsimp only [layers]; omega
  have addBack : layers+1 = available := Nat.sub_add_cancel (by omega)
  have layerFit : layers ≤ q := (Nat.sub_le _ _).trans (min_le_left _ _)
  have reserve : (layers+1)*q^2 ≤ b := by
    rw [addBack]
    exact (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  refine ⟨layers,layerLarge,layerFit,reserve,?_,?_⟩
  · rcases le_total q (b/q^2) with full | restricted
    · have fullLayers : layers+1 = q := addBack.trans (min_eq_left full)
      have scale : 15*q^3 ≤ 16*(layers*q^2) := calc
        _ = (15*q)*q^2 := by ring
        _ ≤ (16*layers)*q^2 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
      omega
    · have fractionLayers : layers+1 = b/q^2 := addBack.trans (min_eq_right restricted)
      have next := Nat.lt_mul_div_succ b squarePos
      have cap : b < (layers+2)*q^2 := by
        rw [show layers+2 = b/q^2+1 by omega,Nat.mul_comm]
        exact next
      calc
        _ ≤ (layers+2)*q^2 := cap.le
        _ ≤ (4*layers)*q^2 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
  · rcases le_total q (b/q^2) with full | restricted
    · have fullLayers : layers+1 = q := addBack.trans (min_eq_left full)
      calc
        _ ≤ a*q := Nat.mul_le_mul ordered slopeFit
        _ ≤ a*(layers+2) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    · have fractionLayers : layers+1 = b/q^2 := addBack.trans (min_eq_right restricted)
      have next := Nat.lt_mul_div_succ b squarePos
      have cap : b < (layers+2)*q^2 := by
        rw [show layers+2 = b/q^2+1 by omega,Nat.mul_comm]
        exact next
      calc
        _ ≤ ((layers+2)*q^2)*slopes := Nat.mul_le_mul_right _ cap.le
        _ = (layers+2)*(slopes*q^2) := by ring
        _ ≤ (layers+2)*a := Nat.mul_le_mul_left _ budget
        _ = _ := by ring

private theorem literal_full_three_with_spare_layer {n p v r q : ℕ} (large : 16 ≤ q)
    (reserve : v+q^2 ≤ n) (pathsFit : r ≤ p) (pathCap : p ≤ 4*q^3)
    (rows : Fin r → List (Fin v)) (injective : Function.Injective rows)
    (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup) (free : BridgeFree (Before rows) 3) :
    ∃ candidate : Fin p → List (Fin n), Function.Injective candidate ∧
      (∀ i, candidate i ≠ [] ∧ (candidate i).Nodup) ∧ BridgeFree (Before candidate) 3 ∧
      (∑ i, (rows i).length) ≤ ∑ i, (candidate i).length := by
  let spare := n-v
  let extra := p-r
  have enoughVertices : q^2 ≤ spare := by dsimp only [spare]; omega
  have firstSide : 8*q ≤ spare/2 := by
    have bound : 16*q ≤ q^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ large
    omega
  have secondSide : q^2 ≤ 2*(spare-spare/2) := by omega
  have space : 8*q^3 ≤ 2*((spare/2)*(spare-spare/2)) := calc
    _ = (8*q)*q^2 := by ring
    _ ≤ (spare/2)*(2*(spare-spare/2)) := Nat.mul_le_mul firstSide secondSide
    _ = _ := by ring
  have enough : extra ≤ spare+2*((spare/2)*(spare-spare/2)) := by
    have extraCap : extra ≤ 4*q^3 := (Nat.sub_le _ _).trans pathCap
    omega
  have vertexSum : v+spare = n := Nat.add_sub_of_le (by omega)
  have pathSum : r+extra = p := Nat.add_sub_of_le pathsFit
  obtain ⟨padding,padDistinct,padRows,padFree⟩ := literal_full_three_feasible_iff.mpr enough
  obtain ⟨joined,joinedDistinct,joinedRows,joinedFree,joinedMass⟩ :=
    exists_literal_full_disjoint_union rows padding injective padDistinct valid padRows free padFree
  let Output (v' r' : ℕ) : Prop := ∃ candidate : Fin r' → List (Fin v'), Function.Injective candidate ∧
    (∀ i, candidate i ≠ [] ∧ (candidate i).Nodup) ∧ BridgeFree (Before candidate) 3 ∧
    (∑ i, (rows i).length) ≤ ∑ i, (candidate i).length
  have combined : Output (v+spare) (r+extra) :=
    ⟨joined,joinedDistinct,joinedRows,joinedFree,by rw [joinedMass]; omega⟩
  rwa [vertexSum,pathSum] at combined

/-- At cutoff three, when both budgets are at least `8192³` and within
a factor two, a full-three witness meets both budgets and the four
starting-average caps at the literal half maximum. It keeps at least
one sixteenth of the maximum. -/
theorem localOrderDistinctExtremal_frozen_full_three_at_budget_ratio_two {n p : ℕ}
    (large : 8192^3 ≤ min n p) (ratio : max n p ≤ 2*min n p) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ v ≤ n, ∃ r ≤ p, ∃ rows : Fin r → List (Fin v),
        Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (∑ i, (rows i).length) ≤ M ∧ M ≤ 16*(∑ i, (rows i).length) ∧
        frozenListCaps n p M rows := by
  let a := max n p
  let b := min n p
  have bPos : 0 < b := Nat.lt_of_lt_of_le (by decide) large
  have hn : 0 < n := bPos.trans_le (min_le_left _ _)
  have hp : 0 < p := bPos.trans_le (min_le_right _ _)
  have ba : b ≤ a := (min_le_left n p).trans (le_max_left n p)
  obtain ⟨m,slopes,mPos,slopeLarge,slopeFit,slopeBudget,slopeCover,globalEnvelope,cubic⟩ :=
    exists_dyadic_slope_scale (large.trans ba)
  let q := 2^m
  have qLarge : 4096 ≤ q := slopeLarge.trans slopeFit
  obtain ⟨layers,layerLarge,layerFit,reserve,layerCover,product⟩ :=
    exists_layer_width_with_reserve ba ratio slopeLarge slopeFit slopeBudget globalEnvelope
  let V := layers*q^2
  let R := slopes*q^2
  let W := V*slopes
  have smallFit : V ≤ b := calc
    _ ≤ (layers+1)*q^2 := Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := reserve
  have massBalance : R*layers = W := by dsimp only [R,W,V]; ring
  obtain ⟨v,r,len,deg,orientation⟩ : ∃ v r len deg,
      (n = b ∧ p = a ∧ v = V ∧ r = R ∧ len = layers ∧ deg = slopes) ∨
      (n = a ∧ p = b ∧ v = R ∧ r = V ∧ len = slopes ∧ deg = layers) := by
    rcases le_total n p with h | h
    · exact ⟨V,R,layers,slopes,Or.inl ⟨(min_eq_left h).symm,(max_eq_right h).symm,rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨R,V,slopes,layers,Or.inr ⟨(max_eq_left h).symm,(min_eq_right h).symm,rfl,rfl,rfl,rfl⟩⟩
  have fit : v ≤ n ∧ r ≤ p := by
    rcases orientation with ⟨nv,pr,rfl,rfl,_,_⟩ | ⟨nv,pr,rfl,rfl,_,_⟩
    · exact ⟨smallFit.trans_eq nv.symm,slopeBudget.trans_eq pr.symm⟩
    · exact ⟨slopeBudget.trans_eq nv.symm,smallFit.trans_eq pr.symm⟩
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let K := GaloisField 2 m
  let : Fintype K := Fintype.ofFinite K
  have card : Fintype.card K = q := (Nat.card_eq_fintype_card).symm.trans (GaloisField.card 2 m mPos.ne')
  have fieldShape : (v = layers*(Fintype.card K)^2 ∧ r = slopes*(Fintype.card K)^2 ∧
      len = layers ∧ deg = slopes) ∨ (v = slopes*(Fintype.card K)^2 ∧ r = layers*(Fintype.card K)^2 ∧
      len = slopes ∧ deg = layers) := by
    rw [card]
    exact orientation.elim (fun h => Or.inl h.2.2) (fun h => Or.inr h.2.2)
  obtain ⟨rows,injective,lengths,free,mass,degrees,_⟩ := wenger_full_three_rows_on_slopes_and_layers K
    layerLarge (by omega : 2 ≤ slopes) (card.symm ▸ layerFit) (card.symm ▸ slopeFit) fieldShape
  have lenLarge : 2 ≤ len := by
    rcases orientation with ⟨_,_,_,_,rfl,_⟩ | ⟨_,_,_,_,rfl,_⟩ <;> omega
  have long (i) : 2 ≤ (rows i).length := (lengths i).2.symm ▸ lenLarge
  have present (i) : rows i ≠ [] ∧ (rows i).Nodup :=
    ⟨List.length_pos_iff.mp (lt_of_lt_of_le (by decide) (long i)),(lengths i).1⟩
  obtain ⟨candidate,candidateDistinct,candidateRows,candidateFree,candidateMass⟩ :
      ∃ candidate : Fin p → List (Fin n), Function.Injective candidate ∧
        (∀ i, candidate i ≠ [] ∧ (candidate i).Nodup) ∧ BridgeFree (Before candidate) 3 ∧
        (∑ i, (rows i).length) ≤ ∑ i, (candidate i).length := by
    rcases orientation with ⟨nv,pr,rfl,rfl,_,_⟩ | ⟨nv,pr,rfl,rfl,_,_⟩
    · have spare : V+q^2 ≤ n := calc
        _ = (layers+1)*q^2 := by dsimp only [V]; ring
        _ ≤ b := reserve
        _ = _ := nv.symm
      have pathCap : p ≤ 4*q^3 := by change 4*a ≤ 15*q^3 at globalEnvelope; omega
      exact literal_full_three_with_spare_layer (by omega) spare fit.2 pathCap rows injective present free
    · have rowLe : p ≤ n := by omega
      simpa only [one_mul] using exists_literal_full_disjoint_copies_with_singletons (t := 1)
        rows (fun i => (lengths i).1) long (by decide) free
        (by simpa only [one_mul] using fit.1)
        (by simpa only [one_mul] using fit.2)
        (by simpa only [one_mul] using (Nat.sub_le p V).trans rowLe)
  obtain ⟨paths,distinct,valid,half,maximal,_,_⟩ := localOrderDistinctExtremal_isDense (k := 3) true hp
    ⟨candidate,candidateDistinct,candidateRows,candidateFree.halfFree⟩
  let M := ∑ i, (paths i).length
  have massExact : (∑ i, (rows i).length) = W := by
    rcases orientation with ⟨_,_,_,rfl,rfl,_⟩ | ⟨_,_,_,rfl,rfl,_⟩
    · exact mass.trans massBalance
    · exact mass
  have witnessLe : (∑ i, (rows i).length) ≤ M :=
    candidateMass.trans (maximal candidate candidateDistinct candidateRows candidateFree.halfFree)
  have lower : W ≤ M := massExact.symm.trans_le witnessLe
  have upper : 16*M ≤ 63*(b*slopes) := half_three_mass_scaled_le_min_of_ratio_two hn hp ratio slopeLarge
    cubic paths (fun i => (valid i).2) half le_rfl
  have delta : 128*a ≤ b*slopes := calc
    _ ≤ 256*b := by change a ≤ 2*b at ratio; omega
    _ ≤ slopes*b := Nat.mul_le_mul_right _ (by omega)
    _ = _ := Nat.mul_comm _ _
  have lowerSmall : M ≤ 4*(b*slopes) := by omega
  have lowerLarge : M ≤ 4*(a*layers) := by omega
  have upperSmall : b*slopes ≤ 4*M := calc
    _ ≤ (4*V)*slopes := Nat.mul_le_mul_right _ layerCover
    _ = 4*W := by dsimp only [W]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ lower
  have upperLarge : a*layers ≤ 4*M := calc
    _ ≤ (4*R)*layers := Nat.mul_le_mul_right _ slopeCover
    _ = 4*W := by rw [Nat.mul_assoc,massBalance]
    _ ≤ _ := Nat.mul_le_mul_left _ lower
  have capsAt {budget width : ℕ} (positive : 0 < budget) (lo : M ≤ 4*(budget*width))
      (hi : budget*width ≤ 4*M) :
      (M:ℝ)/(4*(budget:ℝ)) ≤ width ∧ (width:ℝ) ≤ 4*(M:ℝ)/budget := by
    have pos : (0:ℝ) < budget := Nat.cast_pos.mpr positive
    have lowerR : (M:ℝ) ≤ 4*((budget:ℝ)*width) := by exact_mod_cast lo
    have upperR : (budget:ℝ)*width ≤ 4*(M:ℝ) := by exact_mod_cast hi
    refine ⟨(div_le_iff₀ (by positivity)).mpr ?_,(le_div_iff₀ pos).mpr ?_⟩
    · convert lowerR using 1
      ring
    · simpa only [mul_comm (width:ℝ)] using upperR
  have caps : frozenListCaps n p M rows := by
    simp only [frozenListCaps,degrees,fun i => (lengths i).2]
    rcases orientation with ⟨nv,pr,_,_,rfl,rfl⟩ | ⟨nv,pr,_,_,rfl,rfl⟩
    · exact ⟨fun _ => capsAt hn (by rwa [nv]) (by rwa [nv]),fun _ => capsAt hp (by rwa [pr]) (by rwa [pr])⟩
    · exact ⟨fun _ => capsAt hn (by rwa [nv]) (by rwa [nv]),fun _ => capsAt hp (by rwa [pr]) (by rwa [pr])⟩
  have retain : M ≤ 16*(∑ i, (rows i).length) := calc
    _ ≤ 4*(b*slopes) := lowerSmall
    _ ≤ 4*((4*V)*slopes) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ layerCover)
    _ = _ := by rw [massExact]; dsimp only [W]; ring
  exact ⟨paths,distinct,valid,half,maximal,v,fit.1,r,fit.2,rows,injective,present,free,witnessLe,retain,caps⟩

end OnlineReachabilityPreservers
