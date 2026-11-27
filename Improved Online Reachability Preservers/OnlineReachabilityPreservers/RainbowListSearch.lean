import OnlineReachabilityPreservers.SplitAudit

/-! A finite search certificate for full bridge exclusion in small fixtures. -/

namespace OnlineReachabilityPreservers.SourceAudit

local instance decidableRainbowBeforeIn {V I : Type*} [DecidableEq V] (paths : I → List V)
    (i : I) (s t : V) : Decidable (BeforeIn paths i s t) := by
  unfold BeforeIn
  infer_instance

/-- Search for a route of bounded length using each permitted row at most once. -/
def rainbowSearch {V I : Type*} [DecidableEq V] [DecidableEq I] (paths : I → List V) :
    ℕ → List I → V → V → Bool
  | 0, _, s, t => decide (s = t)
  | k+1, allowed, s, t =>
    decide (s = t) || allowed.any (fun i =>
      (paths i).any (fun v => decide (BeforeIn paths i s v) &&
        rainbowSearch paths k (allowed.filter (fun j => decide (j ≠ i))) v t))

/-- Every chain with distinct permitted rows is found by the route search. -/
theorem rainbowSearch_of_chain {V I : Type*} [DecidableEq V] [DecidableEq I]
    (paths : I → List V) {k : ℕ} (v : Fin (k+1) → V) (a : Fin k → I)
    (distinct : Function.Injective a) (allowed : List I)
    (present : ∀ i, a i ∈ allowed) (steps : ∀ i, BeforeIn paths (a i) (v i.castSucc) (v i.succ)) :
    rainbowSearch paths k allowed (v 0) (v (Fin.last k)) = true := by
  induction k generalizing allowed with
  | zero =>
    have same : (Fin.last 0 : Fin 1) = 0 := by decide
    simp [rainbowSearch, same]
  | succ k ih =>
    rw [rainbowSearch, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a 0, present 0, List.any_eq_true.mpr ?_⟩
    have step := steps 0
    refine ⟨v 1, step.2.1, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true step, ?_⟩
    let v' (i : Fin (k+1)) := v i.succ
    let a' (i : Fin k) := a i.succ
    have inj : Function.Injective a' := distinct.comp (Fin.succ_injective _)
    have all (i : Fin k) : a' i ∈ allowed.filter (fun j => decide (j ≠ a 0)) := by
      apply List.mem_filter.mpr
      refine ⟨present i.succ, decide_eq_true ?_⟩
      exact fun eq => Fin.succ_ne_zero i (distinct eq)
    have follows (i : Fin k) : BeforeIn paths (a' i) (v' i.castSucc) (v' i.succ) := by
      simpa only [v', a', Fin.succ_castSucc] using steps i.succ
    simpa only [v', Fin.succ_last, Fin.succ_zero_eq_one] using ih v' a' inj _ all follows

/-- A search excluding alternative routes for every river comparison
certifies full bridge exclusion at every size. -/
theorem isEmpty_bridge_of_rainbowSearch {V : Type*} [DecidableEq V] {p : ℕ}
    (rows : Fin p → List V)
    (none : ∀ (fuel row : Fin p) (x y : V), BeforeIn rows row x y →
      rainbowSearch rows fuel.val ((List.finRange p).filter (fun i => decide (i ≠ row))) x y = false)
    (k : ℕ) : IsEmpty (Bridge (BeforeIn rows) k) := by
  refine ⟨fun bridge => ?_⟩
  have cap := bridge_path_count_le bridge
  rw [Fintype.card_fin] at cap
  let fuel : Fin p := ⟨k+1, by omega⟩
  let allowed := (List.finRange p).filter (fun i => decide (i ≠ bridge.river))
  have present (i : Fin (k+1)) : bridge.arc i ∈ allowed :=
    List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true (bridge.river_ne_arc i).symm⟩
  have found := rainbowSearch_of_chain rows bridge.vertex bridge.arc bridge.distinctArcs allowed present bridge.arcStep
  have absent := none fuel bridge.river _ _ bridge.riverStep
  change rainbowSearch rows (k+1) allowed (bridge.vertex 0) (bridge.vertex (Fin.last (k+1))) = false at absent
  rw [absent] at found
  contradiction

end OnlineReachabilityPreservers.SourceAudit
