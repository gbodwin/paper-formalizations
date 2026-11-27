import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Full cleaning at the starting averages after a length-capped restriction. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Once a subfamily satisfies the original upper length cap, splitting
only vertices and keeping the filled copies yields the original caps
whenever its mass covers the trim and the two peeling charges. -/
theorem regularization_list_frozen_full_of_length_capped_subrows {n p k retention : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) (positive : 0 < retention)
    (B : Finset (Fin p)) (kept : B → List (Fin n)) (sub : ∀ i, (kept i).Sublist (paths i.val))
    (lengthCap : ∀ i, (kept i).length ≤ 4*(∑ j, (paths j).length)/p)
    (margin : let M : ℝ := ((∑ i, (paths i).length : ℕ):ℝ)
      let K : ℝ := ((∑ i, (kept i).length : ℕ):ℝ)
      M/retention ≤ K-K^2/(12*M)-M/4-(M/(4*(p:ℝ)))*B.card) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let copies := splitListVertices kept D
  have keptSimple (i : B) : (kept i).Nodup := (sub i).nodup (simple i.val)
  have originalStep {i : B} {x y : Fin n} (step : Before kept i x y) :
      Before (fun j : B => paths j.val) i x y := listBefore_of_sublist (simple i.val) (sub i) step
  have keptFree : BridgeFree (Before kept) k := fun d bound =>
    ⟨fun bridge => (free bound).false (bridge.mapPaths Subtype.val Subtype.val_injective
      (fun _ _ _ step => originalStep step))⟩
  have copiesFree : BridgeFree (Before copies) k := keptFree.split_list_vertices_any (·.fst)
    (fun {i _ _} step => splitListVertices_step (keptSimple i) step)
  have copiesSimple (i : B) : (copies i).Nodup := splitListVertices_simple kept D i (keptSimple i)
  obtain ⟨width,_,_⟩ := four_average_width hn dense
  change 0 < D at width
  have fit : Fintype.card B ≤ p := by simpa only [Fintype.card_coe,card_univ,Fintype.card_fin] using card_le_univ B
  obtain ⟨filled,full,rest⟩ := splitListVertices_full_block_profile kept width
  have mass : (∑ i, (copies i).length) = ∑ i, (kept i).length :=
    sum_congr rfl (fun i _ => splitListVertices_length kept D i)
  have massCap : (∑ i, (kept i).length) ≤ M := calc
    _ ≤ ∑ i : B, (paths i.val).length := sum_le_sum fun i _ => (sub i).length_le
    _ = ∑ i ∈ B, (paths i).length := B.sum_coe_sort (fun i => (paths i).length)
    _ ≤ M := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have copyLength (i : B) : (copies i).length ≤ 4*M/p :=
    (splitListVertices_length kept D i).le.trans (lengthCap i)
  have degree (v : ListVertexBlockIndex kept D) : (occurrences (fun i => (copies i).toFinset) v).card ≤ D := by
    simpa only [copies,splitListVertices_toFinset] using splitVertices_degree (fun i => (kept i).toFinset) width v
  have remainders : (univ \ filled).card ≤ n := by
    rw [rest,Fintype.card_fin]
  exact regularization_list_frozen_trim_vertices_quadratic (half := false) (M := M) copies copiesSimple copiesFree
    hn hp dense long positive filled full remainders fit copyLength degree
    (mass.trans_le massCap) (by rw [mass,Fintype.card_coe]; exact margin)

private theorem length_capped_full_margin {M K s r : ℝ} (positive : 0 < M)
    (range : s*M ≤ K) (upper : K ≤ M) (scale : s ≤ 1)
    (fee : 1/r ≤ s-s^2/12-1/2) : M/r ≤ K-K^2/(12*M)-M/2 := by
  have sMass : s*M ≤ M := by simpa only [one_mul] using (mul_le_mul_of_nonneg_right scale positive.le)
  have compare : 0 ≤ (K-s*M)*(12*M-K-s*M) :=
    mul_nonneg (sub_nonneg.mpr range) (by linarith only [upper,sMass,positive])
  have first : s*M-(s*M)^2/(12*M) ≤ K-K^2/(12*M) := by
    have denom : 0 < 12*M := by positivity
    apply (mul_le_mul_iff_right₀ denom).mp
    calc
      (12*M)*(s*M-(s*M)^2/(12*M)) = (12*M)*(s*M)-(s*M)^2 := by field_simp [positive.ne']
      _ ≤ (12*M)*K-K^2 := by nlinarith only [compare]
      _ = (12*M)*(K-K^2/(12*M)) := by field_simp [positive.ne']
  have square : (s*M)^2/(12*M) = (s^2/12)*M := by
    field_simp [positive.ne']
  have pay := mul_le_mul_of_nonneg_right fee positive.le
  rw [square] at first
  calc
    _ = (1/r)*M := by ring
    _ ≤ (s-s^2/12-1/2)*M := pay
    _ ≤ _ := by linarith only [first]

/-- At any full cutoff, truncating the original rows at the upper
length cap suffices when it keeps three fifths of the mass, or eight
fifteenths with the larger allowed loss factor. -/
theorem regularization_list_frozen_full_of_truncation {n p k retention : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (range : let M := ∑ i, (paths i).length
      let K := ∑ i, min (4*M/p) (paths i).length
      (16 ≤ retention ∧ 3*M ≤ 5*K) ∨ (128 ≤ retention ∧ 8*M ≤ 15*K)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let K := ∑ i, min (4*M/p) (paths i).length
  let B := (univ : Finset (Fin p))
  let kept (i : B) := (paths i.val).take (4*M/p)
  have lengths (i : B) : (kept i).length = min (4*M/p) (paths i.val).length := List.length_take
  have mass : (∑ i, (kept i).length) = K := calc
    _ = ∑ i : B, min (4*M/p) (paths i.val).length := sum_congr rfl (fun i _ => lengths i)
    _ = _ := B.sum_coe_sort (fun i => min (4*M/p) (paths i).length)
  have K_le_M : K ≤ M := sum_le_sum (fun i _ => min_le_right _ _)
  change (16 ≤ retention ∧ 3*M ≤ 5*K) ∨ (128 ≤ retention ∧ 8*M ≤ 15*K) at range
  have retentionPos : 0 < retention := by rcases range with near | loose <;> omega
  have mr : (0:ℝ) < M := by exact_mod_cast hn.trans_le dense
  have kr : (K:ℝ) ≤ M := by exact_mod_cast K_le_M
  have margin : (M:ℝ)/retention ≤ (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/2 := by
    rcases range with ⟨ret,keeps⟩ | ⟨ret,keeps⟩
    · have keptR : (3:ℝ)*M ≤ 5*(K:ℝ) := by exact_mod_cast keeps
      have largeR : (16:ℝ) ≤ retention := by exact_mod_cast ret
      have fee : (1:ℝ)/retention ≤ 1/16 := one_div_le_one_div_of_le (by norm_num) largeR
      exact length_capped_full_margin mr (s := 3/5) (by linarith only [keptR]) kr
        (by norm_num) (fee.trans (by norm_num))
    · have keptR : (8:ℝ)*M ≤ 15*(K:ℝ) := by exact_mod_cast keeps
      have largeR : (128:ℝ) ≤ retention := by exact_mod_cast ret
      have fee : (1:ℝ)/retention ≤ 1/128 := one_div_le_one_div_of_le (by norm_num) largeR
      exact length_capped_full_margin mr (s := 8/15) (by linarith only [keptR]) kr
        (by norm_num) (fee.trans (by norm_num))
  have count : B.card = p := by simp [B]
  have price : (M:ℝ)/(4*(p:ℝ))*(B.card:ℝ) = (M:ℝ)/4 := by
    rw [count]
    have p0 : (p:ℝ) ≠ 0 := (Nat.cast_pos.mpr hp).ne'
    field_simp [p0]
  exact regularization_list_frozen_full_of_length_capped_subrows paths simple free hn hp dense long
    retentionPos B kept (fun i => List.take_sublist _ _) (fun i => (lengths i).le.trans (min_le_left _ _))
    (by
      change (M:ℝ)/retention ≤ ((∑ i, (kept i).length : ℕ):ℝ)-
        ((∑ i, (kept i).length : ℕ):ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-(M:ℝ)/(4*(p:ℝ))*B.card
      rw [mass,price]
      linarith only [margin])

/-- The same two truncation thresholds yield the literal witness at
full cutoffs of at least two. -/
theorem regularization_list_frozen_full_distinct_of_truncation {n p k retention : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (rows : ∀ i, paths i ≠ [] ∧ (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (range : let M := ∑ i, (paths i).length
      let K := ∑ i, min (4*M/p) (paths i).length
      (16 ≤ retention ∧ 3*M ≤ 5*K) ∨ (128 ≤ retention ∧ 8*M ≤ 15*K)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have retentionBound : 8 ≤ retention := by rcases range with near | loose <;> omega
  obtain ⟨v,vFits,q,qFits,clean,unique,present,simple,full,mass,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (half := false) paths distinct (fun i => (rows i).1)
      (fun i => (rows i).2) free two hn hp dense retentionBound
      (fun long => regularization_list_frozen_full_of_truncation paths (fun i => (rows i).2)
        free hn hp dense long range)
  exact ⟨v,vFits,q,qFits,clean,unique,fun i => ⟨present i,simple i⟩,full,mass,upper,caps⟩

end OnlineReachabilityPreservers
