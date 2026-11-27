import OnlineReachabilityPreservers.UnbalancedBridgeExtrema

/-! Compare the literal half maximum to full witnesses within both budgets. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Through cutoff two, a bridge is a parallel comparison on two rows.
The later row could be its river, so half and full exclusion coincide. -/
theorem halfBridgeFree_iff_full_of_le_two {n p cutoff : ℕ} (paths : Fin p → List (Fin n))
    (short : cutoff ≤ 2) : HalfBridgeFree (Before paths) cutoff ↔ BridgeFree (Before paths) cutoff := by
  refine ⟨?_,fun free => free.halfFree⟩
  intro free s bound
  refine ⟨fun b => ?_⟩
  have zero : s = 0 := by omega
  subst s
  exact no_parallel_list_steps free bound (b.river_ne_arc 0) b.riverStep (b.arcStep 0)

/-- Feasibility in the literal half model supplies an all-size full
witness on at most the same budgets, with mass at least one eighth of
the larger budget. -/
theorem exists_distinct_full_witness_of_half_feasible {n p cutoff : ℕ} (paths : Fin p → List (Fin n))
    (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      (∀ k, BridgeFree (Before clean) k) ∧ max n p ≤ 8*(∑ i, (clean i).length) := by
  by_cases few : p ≤ n
  · let clean (_ : Fin 1) := List.finRange n
    have all (k : ℕ) : BridgeFree (Before clean) k := by
      intro s _
      exact ⟨fun b => b.river_ne_arc 0 (Subsingleton.elim _ _)⟩
    refine ⟨n,le_rfl,1,hp,clean,fun _ _ _ => Subsingleton.elim _ _,?_,fun _ => List.nodup_finRange _,all,?_⟩
    · intro i empty
      have length := congrArg List.length empty
      change (List.finRange n).length = 0 at length
      rw [List.length_finRange] at length
      exact hn.ne' length
    · have mass : (∑ i, (clean i).length) = n := by simp [clean]
      rw [mass,max_eq_left few]
      omega
  let kept (i : Fin p) := (paths i).take 2
  have sub (i : Fin p) : (kept i).Sublist (paths i) := List.take_sublist 2 _
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptFree : HalfBridgeFree (Before kept) cutoff := by
    intro s bound b earlier
    exact free bound (b.mapPaths (id : Fin p → Fin p) Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step)) earlier
  have keptDistinct : Function.Injective kept := by
    intro i j equal
    by_cases long : 2 ≤ (kept i).length
    · by_contra different
      have step : Before kept i ((kept i)[0]'(by omega)) ((kept i)[1]'(by omega)) := by
        refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
        rw [(keptSimple i).idxOf_getElem,(keptSimple i).idxOf_getElem]
        decide
      have parallel : Before kept j ((kept i)[0]'(by omega)) ((kept i)[1]'(by omega)) := by
        unfold SourceAudit.BeforeIn at step ⊢
        rw [← equal]
        exact step
      exact no_parallel_list_steps keptFree two different step parallel
    · have shortJ : ¬ 2 ≤ (kept j).length := equal ▸ long
      have whole {r : Fin p} (short : ¬ 2 ≤ (kept r).length) : kept r = paths r := by
        change ¬ 2 ≤ ((paths r).take 2).length at short
        rw [List.length_take] at short
        exact List.take_of_length_le (by omega)
      exact distinct ((whole long).symm.trans (equal.trans (whole shortJ)))
  have nonzero (i : Fin p) : 1 ≤ (kept i).length := by
    have positive : 0 < (paths i).length := List.length_pos_iff.mpr (nonempty i)
    change 1 ≤ ((paths i).take 2).length
    rw [List.length_take]
    omega
  have keptNonempty (i : Fin p) : kept i ≠ [] := List.length_pos_iff.mp (nonzero i)
  have massLower : p ≤ ∑ i, (kept i).length := calc
    _ = ∑ _i : Fin p, 1 := by simp
    _ ≤ _ := sum_le_sum fun i _ => nonzero i
  have massUpper : (∑ i, (kept i).length) ≤ 2*p := by
    calc
      _ ≤ ∑ _i : Fin p, 2 := sum_le_sum fun i _ => List.length_take_le 2 (paths i)
      _ = _ := by simp [Nat.mul_comm]
  have nLeP := (lt_of_not_ge few).le
  obtain ⟨n',va,p',pa,clean,cleanDistinct,cleanNonempty,cleanSimple,cleanFree,mass,_,_⟩ :=
    regularization_list_frozen_distinct_of_small_mean n kept keptDistinct keptNonempty keptSimple keptFree
      two hn hp (nLeP.trans massLower) massLower (by omega)
  refine ⟨n',va,p',pa,clean,cleanDistinct,cleanNonempty,cleanSimple,?_,?_⟩
  · intro k s _
    exact ⟨fun b => (cleanFree (by
      have size : s+2 ≤ n' := by simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective b.vertex b.distinctVertices
      exact size.trans va)).false b⟩
  · exact (max_eq_right nLeP).trans_le (massLower.trans mass)

/-- In the unbalanced regimes, the literal half mass is within a
constant factor of a distinct nonempty all-size full witness on at
most the original budgets. This needs only half-model feasibility. -/
theorem literal_half_mass_le_full_witness_of_unbalanced_budgets {n p cutoff factor : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) cutoff)
    (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (factorLarge : 3 ≤ factor)
    (budget : UnbalancedBridgeBudgets n p cutoff factor) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      (∀ k, BridgeFree (Before clean) k) ∧ (∑ i, (paths i).length) ≤ (8*factor)*(∑ i, (clean i).length) := by
  obtain ⟨n',va,p',pa,clean,distinctClean,nonemptyClean,simpleClean,freeClean,base⟩ :=
    exists_distinct_full_witness_of_half_feasible paths distinct nonempty simple free two hn hp
  refine ⟨n',va,p',pa,clean,distinctClean,nonemptyClean,simpleClean,freeClean,?_⟩
  calc
    _ ≤ factor*max n p := halfBridgeFree_mass_le_of_unbalanced_budgets paths simple free two hn hp factorLarge budget
    _ ≤ factor*(8*(∑ i, (clean i).length)) := Nat.mul_le_mul_left _ base
    _ = _ := by ring

end OnlineReachabilityPreservers
