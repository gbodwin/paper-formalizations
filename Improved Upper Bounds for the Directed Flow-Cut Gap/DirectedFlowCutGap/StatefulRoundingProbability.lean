import DirectedFlowCutGap.StatefulSamplerProjection
import DirectedFlowCutGap.EncodedRoundingProbability

/-!
# Exact failure amplification with a retained physical state

Only the observable vertex-list length is required to have one fixed marginal
at every entering physical state. Complete output records and ledgers may be
correlated and their distributions may vary with that state. The actual
repeated program and first-on-ties selector are used throughout; proof-side
list laws are not additional executable passes.
-/
namespace DirectedFlowCutGap.StatefulRoundingProbability
open StatefulSamplerProjection EncodedRoundingEntry EncodedRoundingRepetition
variable {A B S : Type}
def listDraw {m : Type → Type} [Monad m] (draw : m A) : ℕ → m (List A)
  | 0 => pure []
  | k+1 => do
    let a ← draw
    let tail ← listDraw draw k
    pure (a::tail)

theorem listDraw_view {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : m A) (view : A → B) (k : ℕ) :
    List.map view <$> listDraw draw k = listDraw (view <$> draw) k := by
  induction k with
  | zero => simp only [listDraw,map_pure,List.map_nil]
  | succ k ih =>
      simp only [listDraw,map_bind,map_pure,List.map_cons,bind_map_left]
      congr 1
      funext a
      rw [← ih]
      simp only [← bind_pure_comp,bind_assoc,pure_bind]

noncomputable section
theorem listDraw_observe (draw : StateT S PMF A) (law : PMF A)
    (h : ∀ state, observe draw state=law) (k : ℕ) (state : S) :
    observe (listDraw draw k) state = listDraw law k := by
  induction k generalizing state with
  | zero => exact observe_pure _ _
  | succ k ih =>
      simp only [listDraw]
      rw [observe_bind _ _ _ (fun a s => by
        have hh := observe_bind (listDraw draw k) (fun tail => pure (a::tail))
          (fun tail => PMF.pure (a::tail)) (fun tail s => observe_pure _ s) s
        rw [ih] at hh
        exact hh),h]
      rfl

theorem listDraw_partial_observe (draw : StateT S PMF A) (view : A → B)
    (law : PMF B) (h : ∀ state, (observe draw state).map view=law)
    (k : ℕ) (state : S) :
    (observe (listDraw draw k) state).map (List.map view)=listDraw law k := by
  rw [← observe_map,listDraw_view]
  exact listDraw_observe (view <$> draw) law (fun s => by rw [observe_map,h]) k state

variable {n : ℕ}
theorem drawMany_outputsM {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : m (Output n)) (k : ℕ) :
    Batch.outputs <$> drawMany draw k = listDraw draw k := by
  induction k with
  | zero => simp only [drawMany,listDraw,map_pure]
  | succ k ih =>
      simp only [drawMany,listDraw,map_bind,map_pure]
      congr 1
      funext first
      rw [← ih]
      simp only [← bind_pure_comp,bind_assoc,pure_bind]

theorem repeat_outputsM {m : Type → Type} [Monad m] [LawfulMonad m]
    (draw : m (Output n)) (extra : ℕ) :
    Result.samples <$> repeatDraws draw extra = listDraw draw (extra+1) := by
  simp only [repeatDraws,listDraw,map_bind,map_pure]
  congr 1
  funext first
  rw [← drawMany_outputsM draw extra]
  simp only [← bind_pure_comp,bind_assoc,pure_bind]

theorem repeat_views_law (draw : StateT S PMF (Output n)) (view : Output n → B)
    (law : PMF B) (h : ∀ state, (observe draw state).map view=law)
    (extra : ℕ) (state : S) :
    (observe (repeatDraws draw extra) state).map (fun r => r.samples.map view) =
      listDraw law (extra+1) := by
  change (observe (repeatDraws draw extra) state).map
    ((List.map view) ∘ Result.samples) = _
  rw [← PMF.map_comp,← observe_map,repeat_outputsM]
  exact listDraw_partial_observe draw view law h (extra+1) state

/-- The concrete selector's threshold event still holds with arbitrary
stateful correlations, because it is a deterministic support property. -/
theorem repeat_threshold_iff (draw : StateT S PMF (Output n))
    (extra threshold : ℕ) (state : S) {r : Result n}
    (hr : r ∈ (observe (repeatDraws draw extra) state).support) :
    threshold < r.selected.vertices.length ↔
      ∀ o ∈ r.samples, threshold < o.vertices.length := by
  obtain ⟨out,hout,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  change out ∈ (PMF.bind _ _).support at hout
  obtain ⟨first,hfirst,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨rest,hrest,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  constructor
  · intro h o ho
    exact h.trans_le (select_minimum first.1 rest.1.outputs o ho)
  · intro h
    exact h _ (select_member first.1 rest.1.outputs)

private theorem pmf_pure {X : Type} (a : X) : (pure a : PMF X)=PMF.pure a := rfl

theorem listDraw_all (draw : PMF A) (P : A → Prop) (k : Nat) :
    (listDraw draw k).toOuterMeasure {xs | ∀ x ∈ xs, P x} =
      (draw.toOuterMeasure {x | P x})^k := by
  classical
  induction k with
  | zero => simp [listDraw,pmf_pure]
  | succ k ih =>
      change (draw.bind fun x => (listDraw draw k).map (List.cons x)).toOuterMeasure _ = _
      rw [PMF.toOuterMeasure_bind_apply]
      have sectionProbability (x : A) :
          ((listDraw draw k).map (List.cons x)).toOuterMeasure {xs | ∀ a ∈ xs, P a} =
            if P x then (draw.toOuterMeasure {x | P x})^k else 0 := by
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hx : P x
        · have he : List.cons x ⁻¹' {xs : List A | ∀ a ∈ xs, P a} =
              {xs | ∀ a ∈ xs, P a} := by ext xs; simp [hx]
          rw [he,ih,ite_eq_left hx]
        · have he : List.cons x ⁻¹' {xs : List A | ∀ a ∈ xs, P a} = ∅ := by
            ext xs; simp [hx]
          rw [he,ite_eq_right hx]
          simp
      simp_rw [sectionProbability]
      rw [pow_succ']
      conv => rhs; lhs; rw [PMF.toOuterMeasure_apply]
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      by_cases hx : P x <;> simp [hx]

/-- Independence is established only for the observed lengths, by composing
the pointwise marginal at every entering state. No full-record iid law is assumed. -/
theorem repeat_threshold_probability (draw : StateT S PMF (Output n)) (law : PMF ℕ)
    (h : ∀ state, (observe draw state).map (fun o => o.vertices.length)=law)
    (extra threshold : ℕ) (state : S) :
    (observe (repeatDraws draw extra) state).toOuterMeasure
      {r | threshold < r.selected.vertices.length} =
        (law.toOuterMeasure {k | threshold < k})^(extra+1) := by
  calc
    _ = (observe (repeatDraws draw extra) state).toOuterMeasure
        ((fun r => r.samples.map (fun o => o.vertices.length)) ⁻¹'
          {xs | ∀ k ∈ xs, threshold < k}) := by
      apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
      ext r
      constructor
      · intro ⟨hr,hs⟩
        refine ⟨?_,hs⟩
        intro k hk
        obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hk
        exact (repeat_threshold_iff draw extra threshold state hs).mp hr o ho
      · intro ⟨hr,hs⟩
        refine ⟨?_,hs⟩
        apply (repeat_threshold_iff draw extra threshold state hs).mpr
        intro o ho
        exact hr _ (List.mem_map.mpr ⟨o,ho,rfl⟩)
    _ = ((observe (repeatDraws draw extra) state).map
        (fun r => r.samples.map (fun o => o.vertices.length))).toOuterMeasure
          {xs | ∀ k ∈ xs, threshold < k} := by rw [PMF.toOuterMeasure_map_apply]
    _ = _ := by rw [repeat_views_law draw _ law h,listDraw_all]

end
end DirectedFlowCutGap.StatefulRoundingProbability
