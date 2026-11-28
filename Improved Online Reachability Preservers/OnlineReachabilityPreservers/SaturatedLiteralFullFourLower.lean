import OnlineReachabilityPreservers.SaturatedLiteralHalfFull

/-! A balanced cyclic triple of layers gives full-four-free pair rows at the saturated half budgets. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

abbrev CyclicPairPoint (w : ℕ) := Fin 3 ×ₗ Fin w
abbrev CyclicPairRow (w : ℕ) := Fin 3 ×ₗ (Fin w ×ₗ Fin w)

private def pairLayer {w : ℕ} (v : CyclicPairPoint w) : Fin 3 := (ofLex v).1

private def cycleNext (i : Fin 3) : Fin 3 := i + 1

private def cyclePrev (i : Fin 3) : Fin 3 := i - 1

private theorem cyclePrev_next (i : Fin 3) : cyclePrev (cycleNext i) = i := by
  fin_cases i <;> decide

private theorem cycleNext_prev (i : Fin 3) : cycleNext (cyclePrev i) = i := by
  fin_cases i <;> decide

private theorem cycleNext_ne (i : Fin 3) : cycleNext i ≠ i := by
  fin_cases i <;> decide

private theorem cycleNext_thrice_ne (i : Fin 3) :
    cycleNext (cycleNext (cycleNext i)) ≠ cycleNext i := by
  fin_cases i <;> decide

/-- A pair from each layer to the next, with one row per choice of endpoints. -/
def cyclicPairRows {w : ℕ} (i : CyclicPairRow w) : List (CyclicPairPoint w) :=
  let layer := (ofLex i).1
  let u := (ofLex (ofLex i).2).1
  let v := (ofLex (ofLex i).2).2
  [toLex (layer,u),toLex (cycleNext layer,v)]

theorem cyclicPairRows_length {w : ℕ} (i : CyclicPairRow w) : (cyclicPairRows i).length = 2 := rfl

theorem cyclicPairRows_simple {w : ℕ} (i : CyclicPairRow w) : (cyclicPairRows i).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_,by simp⟩
  intro member
  have same := List.mem_singleton.mp member
  exact cycleNext_ne _ (congrArg pairLayer same).symm

theorem cyclicPairRows_injective (w : ℕ) : Function.Injective (@cyclicPairRows w) := by
  intro i j same
  have pairs := List.cons.inj same
  have source := (toLex : (Fin 3 × Fin w) ≃ CyclicPairPoint w).injective pairs.1
  have target := (toLex : (Fin 3 × Fin w) ≃ CyclicPairPoint w).injective (List.cons.inj pairs.2).1
  apply (ofLex : CyclicPairRow w ≃ (Fin 3 × (Fin w ×ₗ Fin w))).injective
  have layer : (ofLex i).1 = (ofLex j).1 := congrArg (fun x : Fin 3 × Fin w => x.1) source
  have left : (ofLex (ofLex i).2).1 = (ofLex (ofLex j).2).1 := congrArg (fun x : Fin 3 × Fin w => x.2) source
  have right : (ofLex (ofLex i).2).2 = (ofLex (ofLex j).2).2 := congrArg (fun x : Fin 3 × Fin w => x.2) target
  refine Prod.ext layer ((ofLex : (Fin w ×ₗ Fin w) ≃ (Fin w × Fin w)).injective ?_)
  exact Prod.ext left right

private theorem cyclicPairRows_step {w : ℕ} {i : CyclicPairRow w} {x y : CyclicPairPoint w}
    (step : Before cyclicPairRows i x y) : cyclicPairRows i = [x,y] ∧ pairLayer y = cycleNext (pairLayer x) := by
  let u : CyclicPairPoint w := toLex ((ofLex i).1,(ofLex (ofLex i).2).1)
  let v : CyclicPairPoint w := toLex (cycleNext (ofLex i).1,(ofLex (ofLex i).2).2)
  have row : cyclicPairRows i = [u,v] := rfl
  obtain ⟨rfl,rfl⟩ := listBefore_endpoints_of_pair row step
  exact ⟨row,rfl⟩

/-- Every arc advances one layer, excluding two- and three-step detours. -/
theorem cyclicPairRows_full_four (w : ℕ) : BridgeFree (Before (@cyclicPairRows w)) 4 := by
  intro s fits
  refine ⟨fun b => ?_⟩
  have possible : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases possible with rfl | rfl | rfl
  · apply b.river_ne_arc 0 (cyclicPairRows_injective w
      ((cyclicPairRows_step b.riverStep).1.trans (cyclicPairRows_step (b.arcStep 0)).1.symm))
  · have first : pairLayer (b.vertex 1) = cycleNext (pairLayer (b.vertex 0)) :=
      (cyclicPairRows_step (b.arcStep 0)).2
    have second : pairLayer (b.vertex 2) = cycleNext (pairLayer (b.vertex 1)) :=
      (cyclicPairRows_step (b.arcStep 1)).2
    have river : pairLayer (b.vertex 2) = cycleNext (pairLayer (b.vertex 0)) :=
      (cyclicPairRows_step b.riverStep).2
    rw [first] at second
    exact cycleNext_ne _ (second.symm.trans river)
  · have first : pairLayer (b.vertex 1) = cycleNext (pairLayer (b.vertex 0)) :=
      (cyclicPairRows_step (b.arcStep 0)).2
    have second : pairLayer (b.vertex 2) = cycleNext (pairLayer (b.vertex 1)) :=
      (cyclicPairRows_step (b.arcStep 1)).2
    have third : pairLayer (b.vertex 3) = cycleNext (pairLayer (b.vertex 2)) :=
      (cyclicPairRows_step (b.arcStep 2)).2
    have river : pairLayer (b.vertex 3) = cycleNext (pairLayer (b.vertex 0)) :=
      (cyclicPairRows_step b.riverStep).2
    rw [second,first] at third
    exact cycleNext_thrice_ne _ (third.symm.trans river)

theorem cyclicPairRows_degree {w : ℕ} (x : CyclicPairPoint w) :
    (occurrences (fun i => (cyclicPairRows i).toFinset) x).card = 2*w := by
  let out : Fin w ↪ CyclicPairRow w := ⟨fun z => toLex ((ofLex x).1,toLex ((ofLex x).2,z)),
    fun _ _ same => congrArg (fun i : CyclicPairRow w => (ofLex (ofLex i).2).2) same⟩
  let into : Fin w ↪ CyclicPairRow w := ⟨fun z => toLex (cyclePrev (ofLex x).1,toLex (z,(ofLex x).2)),
    fun _ _ same => congrArg (fun i : CyclicPairRow w => (ofLex (ofLex i).2).1) same⟩
  let outgoing := (univ : Finset (Fin w)).map out
  let incoming := (univ : Finset (Fin w)).map into
  have split : occurrences (fun i => (cyclicPairRows i).toFinset) x = outgoing ∪ incoming := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,cyclicPairRows,List.mem_cons,List.not_mem_nil,
      or_false,mem_union,outgoing,incoming,mem_map,mem_univ,true_and]
    constructor
    · rintro (eq | eq)
      · exact Or.inl ⟨(ofLex (ofLex i).2).2,by unfold out; rw [eq]; rfl⟩
      · exact Or.inr ⟨(ofLex (ofLex i).2).1,by
          unfold into
          rw [eq]
          change toLex (cyclePrev (cycleNext (ofLex i).1),
            toLex ((ofLex (ofLex i).2).1,(ofLex (ofLex i).2).2)) = i
          rw [cyclePrev_next]
          rfl⟩
    · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
      · exact Or.inl rfl
      · apply Or.inr
        change x = toLex (cycleNext (cyclePrev (ofLex x).1),(ofLex x).2)
        rw [cycleNext_prev]
        rfl
  have apart : Disjoint outgoing incoming := by
    apply disjoint_left.mpr
    intro i a b
    obtain ⟨u,_,sameOut⟩ := mem_map.mp a
    obtain ⟨v,_,sameIn⟩ := mem_map.mp b
    have conflict : (ofLex x).1 = cyclePrev (ofLex x).1 :=
      congrArg (fun i : CyclicPairRow w => (ofLex i).1) (sameOut.trans sameIn.symm)
    have next := congrArg cycleNext conflict
    rw [cycleNext_prev] at next
    exact cycleNext_ne _ next
  rw [split,card_union_of_disjoint apart]
  simp [outgoing,incoming,two_mul]

private theorem cyclicPairRow_card (w : ℕ) : Fintype.card (CyclicPairRow w) = 3*(w*w) := by
  rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin]

/-- Every row contributes two visits among the three ordered layer pairs. -/
theorem cyclicPairRows_mass (w : ℕ) : (∑ i : CyclicPairRow w, (cyclicPairRows i).length) = 6*(w*w) := by
  simp only [cyclicPairRows_length,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,cyclicPairRow_card]
  ring

/-- Balanced cyclic pair rows attain two thirds of the vertex square
up to an arbitrarily small quadratic error, within the saturated
literal half budgets and all four starting-average caps. -/
theorem frozen_full_four_cyclic_pairs_at_saturated_half_budget (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n →
      let p := n+n.choose 2+1
      let M := n^2+2
      ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
        (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) 4 ∧
        (2/3-ε)*(n:ℝ)^2 ≤ ((∑ i, (rows i).length : ℕ):ℝ) ∧
        (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  refine ⟨max 4 ⌈3/ε⌉₊,?_⟩
  intro n large
  let p := n+n.choose 2+1
  let M := n^2+2
  let w := n/3
  have nLarge : 4 ≤ n := (le_max_left _ _).trans large
  have vFit : 3*w ≤ n := by dsimp [w]; omega
  have vNear : n ≤ 3*w+2 := by dsimp [w]; omega
  have cap : n+1 ≤ 8*w := by omega
  have model : 2*p = M+n := by
    have twice := twice_choose_two_add_self n
    dsimp [p,M]
    omega
  have squared := Nat.pow_le_pow_left vFit 2
  rw [show (3*w)^2 = 9*(w*w) by ring] at squared
  have qFit : 3*(w*w) ≤ p := by dsimp [M] at model; omega
  let rows := relabelListPathsFin (@cyclicPairRows w)
  have countV : Fintype.card (CyclicPairPoint w) = 3*w := by
    rw [Fintype.card_congr ofLex,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
  have countQ := cyclicPairRow_card w
  obtain ⟨simple,free,preservesMass,degrees,lengths⟩ := relabelListPathsFin_spec (@cyclicPairRows w)
    cyclicPairRows_simple (half := false) (cyclicPairRows_full_four w)
  change BridgeFree (Before rows) 4 at free
  have len (i : Fin (Fintype.card (CyclicPairRow w))) : (rows i).length = 2 :=
    (lengths i).trans (cyclicPairRows_length _)
  have degree (a : Fin (Fintype.card (CyclicPairPoint w))) :
      (occurrences (fun i => (rows i).toFinset) a).card = 2*w :=
    (degrees a).trans (cyclicPairRows_degree _)
  have mass := preservesMass.trans (cyclicPairRows_mass w)
  have distinct := nontrivial_halfFree_paths_injective simple (fun i => by rw [len])
    (by decide : 2 ≤ 4) free.halfFree
  refine ⟨Fintype.card (CyclicPairPoint w),countV ▸ ?_,Fintype.card (CyclicPairRow w),countQ ▸ ?_,
    rows,distinct,fun i => ⟨List.length_pos_iff.mp (by rw [len]; decide),simple i⟩,free,?_,?_,?_⟩
  · exact vFit
  · exact qFit
  · have size : (3:ℝ)/ε ≤ n :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right 4 _).trans large))
    have epsN : (3:ℝ) ≤ (n:ℝ)*ε := (div_le_iff₀ positive).mp size
    have absorb := mul_le_mul_of_nonneg_right epsN (show 0 ≤ (n:ℝ) by positivity)
    have near : (n:ℝ) ≤ 3*(w:ℝ)+2 := by exact_mod_cast vNear
    have nReal : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have spread := (sq_le_sq₀ (sub_nonneg.mpr nReal)
      (show 0 ≤ 3*(w:ℝ) by positivity)).mpr (show (n:ℝ)-2 ≤ 3*(w:ℝ) by linarith only [near])
    have nonnegative : (0:ℝ) ≤ n := by positivity
    rw [mass]
    push_cast
    nlinarith only [spread,absorb,nonnegative]
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

end OnlineReachabilityPreservers
