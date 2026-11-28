import OnlineReachabilityPreservers.SaturatedLiteralFullFour

/-! Sharp mass comparison at full cutoff three and the saturated literal half budget. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Keep the two directions of every pair between two equal layers. -/
abbrev BalancedOppositePair (w : ℕ) := Bool ×ₗ (Fin w ×ₗ Fin w)

private def oppositePairIndex {w : ℕ} (i : BalancedOppositePair w) : TwoLayerRow w w :=
  Sum.inl ((ofLex i).1,ofLex (ofLex i).2)

/-- Every pair between the two layers is listed in both orders. -/
def balancedOppositePairRows {w : ℕ} (i : BalancedOppositePair w) : List (Fin (w+w)) :=
  twoLayerBidirectionalRows (oppositePairIndex i)

private theorem oppositePairIndex_injective (w : ℕ) : Function.Injective (@oppositePairIndex w) := by
  intro i j equal
  have raw := Sum.inl.inj equal
  have dir : (ofLex i).1 = (ofLex j).1 := congrArg (fun p : Bool × Fin w × Fin w => p.1) raw
  have pair : ofLex (ofLex i).2 = ofLex (ofLex j).2 := congrArg (fun p : Bool × Fin w × Fin w => p.2) raw
  exact ofLex.injective (Prod.ext dir (ofLex.injective pair))

theorem balancedOppositePairRows_simple {w : ℕ} (i : BalancedOppositePair w) :
    (balancedOppositePairRows i).Nodup := by
  cases order : (ofLex i).1 <;>
    simp [balancedOppositePairRows,oppositePairIndex,twoLayerBidirectionalRows,order,-Fin.natAdd_eq_addNat,layer_vertices_different,
      Ne.symm (layer_vertices_different (ofLex (ofLex i).2).1 (ofLex (ofLex i).2).2)]

theorem balancedOppositePairRows_length {w : ℕ} (i : BalancedOppositePair w) :
    (balancedOppositePairRows i).length = 2 := by
  cases order : (ofLex i).1 <;>
    simp [balancedOppositePairRows,oppositePairIndex,twoLayerBidirectionalRows,order]

theorem balancedOppositePairRows_full_three (w : ℕ) :
    BridgeFree (Before (@balancedOppositePairRows w)) 3 := by
  intro k fits
  exact ⟨fun b => (twoLayerBidirectionalRows_full_three w w fits).false
    (b.mapPaths oppositePairIndex (oppositePairIndex_injective w) (fun _ _ _ h => h))⟩

private theorem left_mem_oppositePair {w : ℕ} (x : Fin w) (i : BalancedOppositePair w) :
    Fin.castAdd w x ∈ balancedOppositePairRows i ↔ x = (ofLex (ofLex i).2).1 := by
  cases order : (ofLex i).1 <;>
    simp [balancedOppositePairRows,oppositePairIndex,twoLayerBidirectionalRows,order,-Fin.natAdd_eq_addNat,layer_vertices_different]

private theorem right_mem_oppositePair {w : ℕ} (x : Fin w) (i : BalancedOppositePair w) :
    Fin.natAdd w x ∈ balancedOppositePairRows i ↔ x = (ofLex (ofLex i).2).2 := by
  have right : Function.Injective (Fin.natAdd w : Fin w → Fin (w+w)) :=
    fun _ _ eq => Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq))
  cases order : (ofLex i).1 <;>
    simp [balancedOppositePairRows,oppositePairIndex,twoLayerBidirectionalRows,order,-Fin.natAdd_eq_addNat,right.eq_iff,
      Ne.symm (layer_vertices_different (ofLex (ofLex i).2).1 x)]

theorem balancedOppositePairRows_degree {w : ℕ} (x : Fin (w+w)) :
    (occurrences (fun i => (balancedOppositePairRows i).toFinset) x).card = 2*w := by
  obtain ⟨i,rfl⟩ := (@finSumFinEquiv w w).surjective x
  rcases i with u | v
  · let fill : Bool × Fin w ↪ BalancedOppositePair w :=
      ⟨fun pair => toLex (pair.1,toLex (u,pair.2)),by
        intro a b same
        have tag := congrArg (fun j : BalancedOppositePair w => (ofLex j).1) same
        have point := congrArg (fun j : BalancedOppositePair w => (ofLex (ofLex j).2).2) same
        exact Prod.ext tag point⟩
    have inner : occurrences (fun i => (balancedOppositePairRows i).toFinset) (Fin.castAdd w u) =
        (univ : Finset (Bool × Fin w)).map fill := by
      ext j
      simp only [mem_occurrences,List.mem_toFinset,left_mem_oppositePair,mem_map,mem_univ,true_and]
      constructor
      · intro coordinate
        exact ⟨((ofLex j).1,(ofLex (ofLex j).2).2),by unfold fill; rw [coordinate]; rfl⟩
      · rintro ⟨pair,rfl⟩
        rfl
    change (occurrences (fun i => (balancedOppositePairRows i).toFinset) (Fin.castAdd w u)).card = _
    rw [inner,card_map,card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  · let fill : Bool × Fin w ↪ BalancedOppositePair w :=
      ⟨fun pair => toLex (pair.1,toLex (pair.2,v)),by
        intro a b same
        have tag := congrArg (fun j : BalancedOppositePair w => (ofLex j).1) same
        have point := congrArg (fun j : BalancedOppositePair w => (ofLex (ofLex j).2).1) same
        exact Prod.ext tag point⟩
    have inner : occurrences (fun i => (balancedOppositePairRows i).toFinset) (Fin.natAdd w v) =
        (univ : Finset (Bool × Fin w)).map fill := by
      ext j
      simp only [mem_occurrences,List.mem_toFinset,right_mem_oppositePair,mem_map,mem_univ,true_and]
      constructor
      · intro coordinate
        exact ⟨((ofLex j).1,(ofLex (ofLex j).2).1),by unfold fill; rw [coordinate]; rfl⟩
      · rintro ⟨pair,rfl⟩
        rfl
    change (occurrences (fun i => (balancedOppositePairRows i).toFinset) (Fin.natAdd w v)).card = _
    rw [inner,card_map,card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]

private theorem balancedOppositePair_card (w : ℕ) : Fintype.card (BalancedOppositePair w) = 2*(w*w) := by
  rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_bool,
    Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin]

theorem balancedOppositePairRows_mass (w : ℕ) :
    (∑ i : BalancedOppositePair w, (balancedOppositePairRows i).length) = 4*(w*w) := by
  simp only [balancedOppositePairRows_length,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,balancedOppositePair_card]
  ring

/-- The double orientation of a balanced bipartite graph witnesses
full-three-free mass at least (1 − ε) times the original vertex square,
within both saturated half budgets and all four original caps. -/
theorem frozen_full_three_opposite_pairs_at_saturated_half_budget (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n →
      let p := n+n.choose 2+1
      let M := n^2+2
      ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (1-ε)*(n:ℝ)^2 ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
        (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  refine ⟨max 3 ⌈2/ε⌉₊,?_⟩
  intro n large
  let p := n+n.choose 2+1
  let M := n^2+2
  let w := n/2
  have nLarge : 3 ≤ n := (le_max_left _ _).trans large
  have vFits : w+w ≤ n := by dsimp [w]; omega
  have vNear : n ≤ 2*w+1 := by dsimp [w]; omega
  have cap : n+1 ≤ 8*w := by omega
  have model : 2*p = M+n := by
    have twice := twice_choose_two_add_self n
    dsimp [p,M]
    omega
  have squares := Nat.pow_le_pow_left vFits 2
  rw [show (w+w)^2 = 4*(w*w) by ring] at squares
  have qFits : 2*(w*w) ≤ p := by dsimp [M] at model; omega
  let rows := relabelListPathsFin (@balancedOppositePairRows w)
  have vFitOrdinal : Fintype.card (Fin (w+w)) ≤ n := by simpa only [Fintype.card_fin] using vFits
  have qFitOrdinal : Fintype.card (BalancedOppositePair w) ≤ p := by
    rw [balancedOppositePair_card]
    exact qFits
  obtain ⟨simple,free,preservesMass,degrees,lengths⟩ :=
    relabelListPathsFin_spec (@balancedOppositePairRows w) balancedOppositePairRows_simple
      (half := false) (balancedOppositePairRows_full_three w)
  change BridgeFree (Before rows) 3 at free
  have len (i : Fin (Fintype.card (BalancedOppositePair w))) : (rows i).length = 2 :=
    (lengths i).trans (balancedOppositePairRows_length _)
  have degree (a : Fin (Fintype.card (Fin (w+w)))) :
      (occurrences (fun i => (rows i).toFinset) a).card = 2*w :=
    (degrees a).trans (balancedOppositePairRows_degree _)
  have mass := preservesMass.trans (balancedOppositePairRows_mass w)
  have distinct := nontrivial_halfFree_paths_injective simple (fun i => by rw [len])
    (by decide : 2 ≤ 3) free.halfFree
  refine ⟨Fintype.card (Fin (w+w)),vFitOrdinal,Fintype.card (BalancedOppositePair w),qFitOrdinal,
    rows,distinct,fun i => ⟨List.length_pos_iff.mp (by rw [len]; decide),simple i⟩,free,?_,?_,?_⟩
  · have size : (2:ℝ)/ε ≤ n :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right 3 _).trans large))
    have epsN := (div_le_iff₀ positive).mp size
    have absorb := mul_le_mul_of_nonneg_right epsN (show 0 ≤ (n:ℝ) by positivity)
    have near : (n:ℝ) ≤ 2*(w:ℝ)+1 := by exact_mod_cast vNear
    have nReal : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have spread := (sq_le_sq₀ (sub_nonneg.mpr nReal)
      (show 0 ≤ 2*(w:ℝ) by positivity)).mpr (show (n:ℝ)-1 ≤ 2*(w:ℝ) by linarith only [near])
    rw [mass]
    push_cast
    nlinarith only [spread,absorb]
  · rw [mass]
    omega
  · constructor
    · intro x
      rw [degree]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
        have raw : M ≤ (2*w)*(4*n) := calc
          _ ≤ n^2+n := by dsimp [M]; omega
          _ = (n+1)*n := by ring
          _ ≤ (8*w)*n := Nat.mul_le_mul_right n cap
          _ = _ := by ring
        exact_mod_cast raw
      · apply (le_div_iff₀ (by positivity : (0:ℝ) < n)).mpr
        have raw : (2*w)*n ≤ n^2 := by rw [pow_two]; exact Nat.mul_le_mul_right n (by omega)
        exact_mod_cast raw.trans (show n^2 ≤ 4*M by dsimp [M]; omega)
    · intro i
      rw [len]
      have pPos : 0 < p := by dsimp [p]; omega
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < 4*(p:ℝ))).mpr
        exact_mod_cast (show M ≤ 2*(4*p) by omega)
      · apply (le_div_iff₀ (by positivity : (0:ℝ) < p)).mpr
        have nSmall : n ≤ M := by
          have product := Nat.le_mul_self n
          dsimp [M]
          rw [pow_two]
          omega
        exact_mod_cast (show 2*p ≤ 4*M by omega)

/-- For full cutoff at least three, literal full mass is at most the
vertex square plus an arbitrarily small quadratic error. -/
theorem literal_full_mass_le_square_of_cutoff_three (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n v q k : ℕ}, N ≤ n → v ≤ n → 3 ≤ k → ∀ rows : Fin q → List (Fin v),
      Function.Injective rows → (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) k →
      ((∑ i, (rows i).length : ℕ):ℝ) ≤ (1+ε)*(n:ℝ)^2 := by
  obtain ⟨U,small⟩ := full_three_long_mass_subquadratic_within_vertex_budget (ε/2) (by positivity)
  refine ⟨max U ⌈4/ε⌉₊,?_⟩
  intro n v q k large fits three rows distinct well full
  have few := literal_full_path_count_le_balanced_bipartite rows distinct (fun i => (well i).1)
    (fun i => (well i).2) full three
  let a := v/2
  let b := v-a
  have counts : (q:ℝ) ≤ (v:ℝ)+2*(a:ℝ)*(b:ℝ) := by
    exact_mod_cast (show q ≤ v+2*a*b by
      dsimp [a,b]
      simpa only [Nat.mul_assoc] using few)
  have split : (a:ℝ)+(b:ℝ) = v := by
    exact_mod_cast (Nat.add_sub_of_le (show a ≤ v from Nat.div_le_self _ _))
  have pairs : 4*(a:ℝ)*(b:ℝ) ≤ (v:ℝ)^2 := calc
    _ ≤ ((a:ℝ)+(b:ℝ))^2 := by nlinarith only [sq_nonneg ((a:ℝ)-(b:ℝ))]
    _ = _ := by rw [split]
  have fits' : (v:ℝ) ≤ n := by exact_mod_cast fits
  have square : (v:ℝ)^2 ≤ (n:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left fits 2
  have long := small ((le_max_left U _).trans large) fits three rows (fun i => (well i).2) full
  have mass : ((∑ i, (rows i).length : ℕ):ℝ) ≤ 2*(q:ℝ)+(listMassAboveWidth rows 2:ℝ) := by
    exact_mod_cast list_mass_le_twice_rows_add_long rows
  have grows : (4:ℝ)/ε ≤ n :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right U _).trans large))
  have absorb := mul_le_mul_of_nonneg_right ((div_le_iff₀ positive).mp grows)
    (show 0 ≤ (n:ℝ) by positivity)
  nlinarith only [counts,pairs,fits',square,long,mass,absorb]

/-- At the saturated literal half budget the half mass is exactly
(M=n^2+2). The optimal full-three-free mass lies between
(1 − ε)M and (1 + ε)M for all large n.
The lower witness satisfies both budgets and all four original-average caps. -/
theorem literal_saturated_half_full_three_mass_comparison (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n →
      let p := n+n.choose 2+1
      let M := n^2+2
      (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
        (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ (∀ k, HalfBridgeFree (Before paths) k) ∧
        (∑ i, (paths i).length) = M) ∧
      (∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 3 ∧
        (1-ε)*(M:ℝ) ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
        (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows) ∧
      ∀ {v q : ℕ}, v ≤ n → q ≤ p → ∀ rows : Fin q → List (Fin v), Function.Injective rows →
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) → BridgeFree (Before rows) 3 →
        ((∑ i, (rows i).length : ℕ):ℝ) ≤ (1+ε)*(M:ℝ) := by
  obtain ⟨U,upper⟩ := literal_full_mass_le_square_of_cutoff_three ε positive
  obtain ⟨L,lower⟩ := frozen_full_three_opposite_pairs_at_saturated_half_budget (ε/2) (by positivity)
  let margin := max 2 ⌈4/ε⌉₊
  refine ⟨max (max U L) margin,?_⟩
  intro n large
  let p := n+n.choose 2+1
  have enough := (le_max_left (max U L) margin).trans large
  have nMargin := (le_max_right (max U L) margin).trans large
  have nTwo : 2 ≤ n := (le_max_left _ _).trans nMargin
  obtain ⟨paths,distinct,valid,all⟩ := literal_half_all_of_choose_budget (n := n) (p := p)
    (by simp [p,nTwo])
  have mass := literal_half_mass_at_saturated_four_budget distinct valid (all 4) le_rfl
  have identity := twice_choose_two_add_self n
  obtain ⟨v,vFits,q,qFits,rows,unique,well,free,lowerMass,massFits,caps⟩ := lower ((le_max_right U L).trans enough)
  refine ⟨⟨paths,distinct,valid,all,by omega⟩,⟨v,vFits,q,qFits,rows,unique,well,free,?_,massFits,caps⟩,?_⟩
  · have grows : (4:ℝ)/ε ≤ n :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans nMargin))
    have epsN := (div_le_iff₀ positive).mp grows
    have one : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have nSq : (n:ℝ) ≤ (n:ℝ)^2 := by
      rw [pow_two]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right one (show 0 ≤ (n:ℝ) by positivity)
    have epsSquare := mul_le_mul_of_nonneg_right nSq positive.le
    change (1-ε)*((n^2+2 : ℕ):ℝ) ≤ _
    refine le_trans ?_ lowerMass
    push_cast
    nlinarith only [epsN,epsSquare,positive]
  · intro v q fits _ rows distinct valid full
    have bound := upper ((le_max_left U L).trans enough) fits (le_rfl : 3 ≤ 3) rows distinct valid full
    refine bound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast (Nat.le_add_right (n^2) 2)


end OnlineReachabilityPreservers
