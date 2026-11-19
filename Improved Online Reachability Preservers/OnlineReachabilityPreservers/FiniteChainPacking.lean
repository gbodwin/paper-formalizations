import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort

namespace OnlineReachabilityPreservers

section Chains

variable {n : ℕ} (link : Fin n → Fin n → Prop)
variable (increases : ∀ {a b}, link a b → a < b)

/-- The head of a chain and the number of links from that head. -/
private noncomputable def chainHeadDepth (grow : ∀ {a b}, link a b → a < b) (v : Fin n) : Fin n × ℕ := by
  classical
  exact if h : ∃ u, link u v then
    let previous := chainHeadDepth grow (Classical.choose h)
    (previous.1, previous.2 + 1)
  else (v, 0)
termination_by v.val
decreasing_by exact grow (Classical.choose_spec h)

variable (predUnique : ∀ {a b v}, link a v → link b v → a = b)

include predUnique in
private theorem chainHeadDepth_step {a b : Fin n} (ab : link a b) :
    chainHeadDepth link increases b =
      ((chainHeadDepth link increases a).1, (chainHeadDepth link increases a).2+1) := by
  classical
  rw [chainHeadDepth]
  split
  · rename_i h
    rw [predUnique (Classical.choose_spec h) ab]
  · rename_i absent
    exact (absent ⟨a, ab⟩).elim

private theorem chainHeadDepth_zero {v : Fin n} (zero : (chainHeadDepth link increases v).2 = 0) :
    (chainHeadDepth link increases v).1 = v := by
  classical
  rw [chainHeadDepth] at zero ⊢
  split at zero
  · simp at zero
  · rename_i absent
    rw [dite_eq_right absent]

private theorem chainHeadDepth_find_prev {v : Fin n} (nonzero : (chainHeadDepth link increases v).2 ≠ 0) :
    ∃ u, link u v := by
  classical
  by_contra absent
  apply nonzero
  rw [chainHeadDepth, dite_eq_right absent]

variable (succUnique : ∀ {v a b}, link v a → link v b → a = b)

include predUnique succUnique in
private theorem chainHeadDepth_unique_depth (d : ℕ) {a b : Fin n}
    (depthA : (chainHeadDepth link increases a).2 = d)
    (depthB : (chainHeadDepth link increases b).2 = d)
    (sameHead : (chainHeadDepth link increases a).1 = (chainHeadDepth link increases b).1) : a = b := by
  induction d generalizing a b with
  | zero =>
    rw [chainHeadDepth_zero link increases depthA, chainHeadDepth_zero link increases depthB] at sameHead
    exact sameHead
  | succ d ih =>
    obtain ⟨u, ua⟩ := chainHeadDepth_find_prev link increases (by rw [depthA]; exact Nat.succ_ne_zero d)
    obtain ⟨v, vb⟩ := chainHeadDepth_find_prev link increases (by rw [depthB]; exact Nat.succ_ne_zero d)
    have stepA := chainHeadDepth_step link increases predUnique ua
    have stepB := chainHeadDepth_step link increases predUnique vb
    rw [stepA] at depthA sameHead
    rw [stepB] at depthB sameHead
    have same := ih (Nat.succ.inj depthA) (Nat.succ.inj depthB) sameHead
    exact succUnique ua (same.symm ▸ vb)

include predUnique succUnique in
private theorem chainHeadDepth_injective : Function.Injective (chainHeadDepth link increases) := by
  intro a b same
  exact chainHeadDepth_unique_depth link increases predUnique succUnique _ rfl
    (congrArg Prod.snd same).symm (congrArg Prod.fst same)

include predUnique in
private theorem chainHeadDepth_step_no_between {a b v : Fin n} (ab : link a b)
    (left : toLex (chainHeadDepth link increases a) < (toLex (chainHeadDepth link increases v) : Fin n ×ₗ ℕ))
    (right : toLex (chainHeadDepth link increases v) < toLex (chainHeadDepth link increases b)) : False := by
  rw [chainHeadDepth_step link increases predUnique ab] at right
  rcases Prod.Lex.lt_iff.mp left with earlier | ⟨equal, shorter⟩
  · rcases Prod.Lex.lt_iff.mp right with later | ⟨equal, _⟩
    · exact lt_asymm earlier later
    · exact earlier.ne equal.symm
  · rcases Prod.Lex.lt_iff.mp right with later | ⟨_, longer⟩
    · exact later.ne equal.symm
    · change (chainHeadDepth link increases a).2 < (chainHeadDepth link increases v).2 at shorter
      change (chainHeadDepth link increases v).2 < (chainHeadDepth link increases a).2 + 1 at longer
      omega

include increases predUnique succUnique in
/-- An order of the vertices in which each chain link is consecutive. -/
theorem exists_chain_packing : ∃ e : Fin n ≃ Fin n,
    ∀ {a b}, link a b → (e b).val = (e a).val + 1 := by
  classical
  let key : Fin n ↪ (Fin n ×ₗ ℕ) :=
    ⟨fun v => toLex (chainHeadDepth link increases v),
      toLex.injective.comp (chainHeadDepth_injective link increases predUnique succUnique)⟩
  let keys := (Finset.univ : Finset (Fin n)).map key
  have cards : keys.card = n := by simp [keys]
  let entering : Fin n ≃ keys := {
    toFun v := ⟨key v, Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
    invFun v := Classical.choose (Finset.mem_map.mp v.property)
    left_inv v := key.injective (Classical.choose_spec (Finset.mem_map.mp
      (Finset.mem_map.mpr ⟨v, Finset.mem_univ _, rfl⟩))).2
    right_inv v := Subtype.ext (Classical.choose_spec (Finset.mem_map.mp v.property)).2 }
  let ranks := (keys.orderIsoOfFin cards).symm
  let e := entering.trans ranks.toEquiv
  refine ⟨e, fun {a b} ab => ?_⟩
  have ordered : e a < e b := by
    apply ranks.strictMono
    change key a < key b
    change toLex (chainHeadDepth link increases a) < toLex (chainHeadDepth link increases b)
    rw [chainHeadDepth_step link increases predUnique ab]
    exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, Nat.lt_succ_self _⟩)
  by_contra different
  have gap : (e a).val + 1 < (e b).val := by omega
  let slot : Fin n := ⟨(e a).val + 1, gap.trans (e b).isLt⟩
  let v := e.symm slot
  have atSlot : e v = slot := e.apply_symm_apply slot
  have before : e a < e v := by rw [atSlot]; exact Nat.lt_succ_self _
  have after : e v < e b := by rw [atSlot]; exact gap
  have left := ranks.strictMono.lt_iff_lt.mp before
  have right := ranks.strictMono.lt_iff_lt.mp after
  exact chainHeadDepth_step_no_between link increases predUnique ab left right

end Chains

end OnlineReachabilityPreservers
