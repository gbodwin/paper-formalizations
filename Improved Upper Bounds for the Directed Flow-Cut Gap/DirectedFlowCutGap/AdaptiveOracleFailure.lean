import DirectedFlowCutGap.EncodedSolverBits

/-!
# Composing checked attempts on adaptive states

Each round can choose a distribution that depends on the complete state
left by the previous rounds. A failed check stops the loop. A bound on
each round's conditional failure probability gives a bound for the
complete loop on a literal finite fair tape.
-/

namespace DirectedFlowCutGap.AdaptiveOracleFailure

open scoped ENNReal
open FiniteDrawTrees

noncomputable def iterate {A : Type} (step : A → PMF (Option A)) :
    ℕ → Option A → PMF (Option A)
  | 0, state => PMF.pure state
  | _ + 1, none => PMF.pure none
  | t + 1, some state => (step state).bind (iterate step t)

private theorem iterate_none {A : Type} (step : A → PMF (Option A)) (T : ℕ) :
    iterate step T none = PMF.pure none := by cases T <;> rfl

theorem iterate_failure {A : Type} (step : A → PMF (Option A)) (ε : ℝ≥0∞)
    (hstep : ∀ a, step a none ≤ ε) (T : ℕ) (state : A) :
    iterate step T (some state) none ≤ (T : ℝ≥0∞) * ε := by
  classical
  induction T generalizing state with
  | zero => simp [iterate, PMF.pure_apply]
  | succ t ih =>
    let p := step state
    change p.bind (iterate step t) none ≤ _
    rw [PMF.bind_apply, ENNReal.tsum_eq_add_tsum_ite none]
    simp only [iterate_none, PMF.pure_apply_self, mul_one]
    calc
      _ ≤ p none + (t : ℝ≥0∞) * ε := by
        refine add_le_add le_rfl ?_
        calc
          _ ≤ ∑' a : Option A, p a * ((t : ℝ≥0∞) * ε) := by
            apply ENNReal.tsum_le_tsum
            intro a
            cases a with
            | none => simp
            | some a =>
              simp only [Option.some_ne_none, ite_false]
              exact mul_le_mul_of_nonneg_left (ih a) zero_le
          _ = _ := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
      _ ≤ ε + (t : ℝ≥0∞) * ε := add_le_add (hstep state) le_rfl
      _ = _ := by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

def tree {A : Type} (step : A → FiniteDrawTrees.Tree (Option A)) : ℕ → Option A → FiniteDrawTrees.Tree (Option A)
  | 0, state => .pure state
  | _ + 1, none => .pure none
  | t + 1, some state => FiniteDrawTrees.bind (step state) (tree step t)

theorem tree_law {A : Type} (step : A → FiniteDrawTrees.Tree (Option A)) (T : ℕ) (state : Option A) :
    ideal (tree step T state) = iterate (fun a => ideal (step a)) T state := by
  induction T generalizing state with
  | zero => rfl
  | succ t ih =>
    cases state with
    | none => rfl
    | some state =>
      change law uniformDraw (FiniteDrawTrees.bind (step state) (tree step t)) = _
      rw [law_bind]
      change (ideal (step state)).bind (fun a => ideal (tree step t a)) =
        (ideal (step state)).bind (iterate (fun a => ideal (step a)) t)
      congr 1
      funext a
      exact ih a

theorem within_tree {A : Type} (step : A → FiniteDrawTrees.Tree (Option A)) (q : ℕ)
    (hstep : ∀ a, Within q (step a)) (T : ℕ) (s : Option A) :
    Within (T * q) (tree step T s) := by
  induction T generalizing s with
  | zero => exact .pure _ _
  | succ T ih =>
    cases s with
    | none => exact .pure _ _
    | some a =>
      simpa only [tree, Nat.succ_mul, Nat.add_comm] using within_bind (hstep a) (tree step T) ih

private theorem within_bind_support {A B : Type} {p : FiniteDrawTrees.Tree A} {q r : ℕ}
    (h : Within q p) (next : A → FiniteDrawTrees.Tree B)
    (hn : ∀ a ∈ (ideal p).support, Within r (next a)) : Within (q + r) (FiniteDrawTrees.bind p next) := by
  induction h with
  | pure q a => exact within_mono (hn a (by simp [ideal, law])) (by omega)
  | @draw q n positive rest children ih =>
    let inst : Nonempty (Fin n) := ⟨⟨0, positive⟩⟩
    have hchildren (j : Fin n) : Within (q + r) (FiniteDrawTrees.bind (rest j) next) := by
      apply ih j
      intro a ha
      apply hn a
      change a ∈ ((uniformDraw n positive).bind (fun b => ideal (rest b))).support
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨j, PMF.mem_support_uniformOfFintype _, ha⟩
    simpa only [FiniteDrawTrees.bind, Nat.add_assoc, Nat.add_comm 1] using
      (Within.draw hchildren : Within (q + r + 1) (.draw n positive (fun j => FiniteDrawTrees.bind (rest j) next)))

theorem within_reachable {A : Type} (step : A → FiniteDrawTrees.Tree (Option A)) (q K : ℕ)
    (safe : ℕ → A → Prop)
    (hstep : ∀ i < K, ∀ a, safe i a → Within q (step a))
    (hmove : ∀ i a b, safe i a → some b ∈ (ideal (step a)).support → safe (i+1) b)
    (T i : ℕ) (s : Option A) (hs : ∀ a, s = some a → safe i a) (hK : i + T ≤ K) :
    Within (T * q) (tree step T s) := by
  induction T generalizing i s with
  | zero => exact .pure _ _
  | succ T ih =>
    cases s with
    | none => exact .pure _ _
    | some a =>
      have ha := hs a rfl
      have proceed : ∀ b ∈ (ideal (step a)).support, Within (T * q) (tree step T b) := by
        intro b hb
        refine ih (i+1) b ?_ (by omega)
        intro next hn
        subst b
        exact hmove i a next ha hb
      simpa only [tree, Nat.succ_mul, Nat.add_comm] using
        within_bind_support (hstep i (by omega) a ha) (tree step T) proceed

theorem binary_tree {A : Type} (step : A → FiniteDrawTrees.Tree (Option A))
    (hstep : ∀ a, LazyFairBitTrees.Binary (step a)) (T : ℕ) (s : Option A) :
    LazyFairBitTrees.Binary (tree step T s) := by
  induction T generalizing s with
  | zero => exact .pure _
  | succ T ih =>
    cases s with
    | none => exact .pure _
    | some a => exact LazyFairBitTrees.binary_bind (hstep a) _ ih

theorem fairTape_failure {A : Type} (step : A → FiniteDrawTrees.Tree (Option A)) (ε : ℝ≥0∞) (q : ℕ)
    (hfail : ∀ a, ideal (step a) none ≤ ε) (hwithin : ∀ a, Within q (step a))
    (hbinary : ∀ a, LazyFairBitTrees.Binary (step a)) (T : ℕ) (state : A) :
    ((EncodedSolverBits.fairTape (T * q)).map (fun tape =>
      ((EncodedSolverBits.run (tree step T (some state)) tape).map Prod.fst).join)) none ≤
      (T : ℝ≥0∞) * ε := by
  let t := tree step T (some state)
  have h := congrArg (PMF.map Option.join)
    (EncodedSolverBits.run_fairTape (within_tree step q hwithin T (some state))
      (binary_tree step hbinary T (some state)))
  simp only [PMF.map_comp, Function.comp_def] at h
  change _ = (ideal t).map id at h
  rw [PMF.map_id] at h
  change ((EncodedSolverBits.fairTape (T * q)).map (fun tape =>
    ((EncodedSolverBits.run t tape).map Prod.fst).join)) none ≤ _
  rw [h, tree_law]
  exact iterate_failure _ ε hfail T state

end DirectedFlowCutGap.AdaptiveOracleFailure
