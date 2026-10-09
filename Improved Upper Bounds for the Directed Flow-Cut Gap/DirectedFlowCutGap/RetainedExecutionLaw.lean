import DirectedFlowCutGap.RetainedSampledExecution
import DirectedFlowCutGap.IntegerClosureAsymptotic

/-!
# Exact law of retained integer execution

Finite tapes are sampled anew from the actual active mask after each retained
stabilization. Their materialized arrays are fed to the existing `execute` and
`run` functions. The resulting full state law is the independently analyzed
flexible law for exactly the selected provider, including every adaptive
restart and its installed weight vector.

Randomness here consists of primitive uniform draws from finite types. A
fair-bit realization and machine-level cost composition remain separate.
-/
namespace DirectedFlowCutGap.RetainedExecutionLaw

open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State FlexibleCandidateSchedule
open RetainedGridState IntegerAdaptiveExecution RetainedTapeInput

/-- Number of primitive finite draws represented by a materialized supply. -/
def primitiveDraws {n L : ℕ} : List (IntegerAdaptiveExecution.Input n L) → ℕ
  | [] => 0
  | i :: inputs => 2 * i.order.length + primitiveDraws inputs

theorem materialize_draws {n L : ℕ} (hL : 0 < L) (a : PairFlags n)
    (t : RetainedTapeInput.Tape L a) :
    2 * (materialize hL a t).order.length = FiniteGridSampler.primitiveDraws t := by
  rw [FiniteGridSampler.primitiveDraws_eq, materialize_order_length, Fintype.card_coe]

noncomputable section
variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}
local notation "P" => selectedProvider H

/-- The actual adaptive supply law. Unused epochs are never drawn. The
stabilized state determines both the permutation size and all active cells. -/
def supplies (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) :
    ℕ → Cache H → PMF (List (IntegerAdaptiveExecution.Input n L))
  | 0, _ => PMF.pure []
  | epochs + 1, c =>
      let a := stabilize Q R restartFuel c
      if a.cache.optimal == 0 then PMF.pure [] else
        (FiniteGridSampler.tapePMF
          (Fintype.card ↥(remainingSet a.cache.state.data.remaining)) L).bind fun t =>
          let i := materialize hL a.cache.state.data.remaining t
          let b := scan Q hL C R a.cache.state.data.current i.cell i.order a.cache
          (supplies Q hL C R restartFuel epochs b.cache).map (i :: ·)

/-- The primitive sampler used in the single-pass monadic interpreter. -/
def sampleTape [NeZero L] (a : PairFlags n) : PMF (RetainedTapeInput.Tape L a) :=
  FiniteGridSampler.tapePMF (Fintype.card ↥(remainingSet a)) L

/-- The supplied-list construction is a proof-side coupling. The online
interpreter does not execute this construction and then replay the list. -/
theorem supplies_executeSampled (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (c : Cache H) :
    (supplies Q hL C R restartFuel epochs c).map
      (fun inputs => (⟨execute Q hL C R restartFuel inputs c, inputs⟩ :
        RetainedSampledExecution.LoggedResult H)) =
      RetainedSampledExecution.executeSampled sampleTape Q hL C R restartFuel epochs c := by
  induction epochs generalizing c with
  | zero =>
      simp only [supplies, PMF.pure_map, RetainedSampledExecution.executeSampled, execute]
      rfl
  | succ epochs ih =>
      simp only [supplies, RetainedSampledExecution.executeSampled]
      split_ifs with hz
      · simp only [PMF.pure_map, execute]
        rfl
      · simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
        change (FiniteGridSampler.tapePMF _ L).bind _ =
          (FiniteGridSampler.tapePMF _ L).bind _
        congr 1
        funext t
        rw [← ih]
        change _ = ((supplies Q hL C R restartFuel epochs _).map _).map _
        rw [PMF.map_comp]
        congr 1
        funext inputs
        simp only [execute, ite_eq_right hz, RetainedSampledExecution.finish, Function.comp_def]

theorem supplies_runSampled (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (s : Code G D L) :
    (supplies Q hL C R restartFuel epochs (refresh Q s)).map
      (fun inputs => (⟨run Q hL C R restartFuel inputs s, inputs⟩ :
        RetainedSampledExecution.LoggedResult H)) =
      RetainedSampledExecution.runSampled sampleTape Q hL C R restartFuel epochs s := by
  change _ = (RetainedSampledExecution.executeSampled sampleTape Q hL C R restartFuel epochs
    (refresh Q s)).map (fun b =>
      (⟨⟨b.result.cache, (refreshWork s).add b.result.work⟩, b.inputs⟩ :
        RetainedSampledExecution.LoggedResult H))
  rw [← supplies_executeSampled]
  rw [PMF.map_comp]
  rfl

/-- The law of the actual single-pass interpreter, including its exact log. -/
def sampledRunLaw (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (s : Code G D L) :
    PMF (RetainedSampledExecution.LoggedResult H) :=
  RetainedSampledExecution.runSampled sampleTape Q hL C R restartFuel epochs s

/-- A law on the complete actual execution result, including retained data
and all optimizer/control counters from that same execution. -/
def executionLaw (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (c : Cache H) : PMF (Result H) :=
  (supplies Q hL C R restartFuel epochs c).map
    (fun inputs => execute Q hL C R restartFuel inputs c)

def outputLaw (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (s : Code G D L) :
    PMF (Finset (Fin n)) :=
  (supplies Q hL C R restartFuel epochs (refresh Q s)).map
    (fun inputs => cutSet (run Q hL C R restartFuel inputs s).cache.state.data.cut)

theorem sampledRunLaw_output (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (s : Code G D L) :
    (sampledRunLaw Q hL C R restartFuel epochs s).map
      (fun d => cutSet d.result.cache.state.data.cut) =
      outputLaw Q hL C R restartFuel epochs s := by
  rw [sampledRunLaw, ← supplies_runSampled, PMF.map_comp]
  rfl

/-- Pointwise refinement is equality of the complete state, including every
selected weight. The existence predicate identifying the provider is erased. -/
theorem execute_exact_reference (Q : Optimizer H) (hL : 0 < L)
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (inputs : List (IntegerAdaptiveExecution.Input n L)) (c : Cache H)
    (hfuel : (interpret c.state).mass < (R : ℝ≥0) ^ restartFuel) :
    interpret (execute Q hL C R restartFuel inputs c).cache.state =
      selectedReference (H := H) hL R hR inputs (interpret c.state) :=
  execute_refines_selectedReference Q hL C R restartFuel hR inputs c hfuel

theorem next_mass_le (Q : Optimizer H) (hL : 0 < L)
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 ≤ (R : ℝ≥0))
    (c : Cache H) (i : IntegerAdaptiveExecution.Input n L) :
    (interpret (scan Q hL C R (stabilize Q R restartFuel c).cache.state.data.current
      i.cell i.order (stabilize Q R restartFuel c).cache).cache.state).mass ≤
      (interpret c.state).mass := by
  exact trace_current_mass_le hR (trace_trans P _
    (stabilize_trace Q hL R restartFuel c)
    (scan_trace Q hL C R (stabilize Q R restartFuel c).cache.state.data.current
      i.cell i.order (stabilize Q R restartFuel c).cache))

/-- Adaptive finite supplies produce exactly the full mathematical solver law.
The common restart budget remains valid because every actual transition
decreases current mass. -/
theorem supplied_state_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (c : Cache H)
    (hfuel : (interpret c.state).mass < (R : ℝ≥0) ^ restartFuel) :
    (supplies Q hL C R restartFuel epochs c).map
        (fun inputs => interpret (execute Q hL C R restartFuel inputs c).cache.state) =
      FlexibleAdaptiveRounding.solve P (R : ℝ≥0) hR epochs (interpret c.state) := by
  induction epochs generalizing c with
  | zero =>
      simp only [supplies, PMF.pure_map, execute, FlexibleAdaptiveRounding.solve]
      rw [stabilize_eq_selectedStabilize Q hL R restartFuel hR c hfuel]
  | succ epochs ih =>
      let a := stabilize Q R restartFuel c
      have hs : interpret a.cache.state =
          (interpret c.state).selectedStabilize P (R : ℝ≥0) hR :=
        stabilize_eq_selectedStabilize Q hL R restartFuel hR c hfuel
      have hz : (a.cache.optimal == 0) = true ↔ (interpret a.cache.state).optimum = 0 := by
        simpa only [beq_iff_eq] using a.cache.zero_correct hL
      rw [FlexibleAdaptiveRounding.solve, ← hs]
      by_cases hzero : a.cache.optimal == 0
      · have hzero' := hz.mp hzero
        simp only [supplies, show stabilize Q R restartFuel c = a from rfl,
          hzero, ite_true, PMF.pure_map, execute, hzero']
      · have hzero' : (interpret a.cache.state).optimum ≠ 0 := fun h => hzero (hz.mpr h)
        simp only [ite_eq_right hzero']
        calc
          _ = (FiniteGridSampler.tapePMF
              (Fintype.card ↥(remainingSet a.cache.state.data.remaining)) L).bind
              (fun t =>
                let i := materialize hL a.cache.state.data.remaining t
                let b := scan Q hL C R a.cache.state.data.current i.cell i.order a.cache
                (supplies Q hL C R restartFuel epochs b.cache).map
                  (fun inputs => interpret
                    (execute Q hL C R restartFuel inputs b.cache).cache.state)) := by
            simp only [supplies, show stabilize Q R restartFuel c = a from rfl,
              PMF.map_bind, PMF.map_comp, Function.comp_def,
              execute, ite_eq_right hzero]
            rfl
          _ = (FiniteGridSampler.tapePMF
              (Fintype.card ↥(remainingSet a.cache.state.data.remaining)) L).bind
              (fun t =>
                let i := materialize hL a.cache.state.data.remaining t
                let b := scan Q hL C R a.cache.state.data.current i.cell i.order a.cache
                FlexibleAdaptiveRounding.solve P (R : ℝ≥0) hR epochs (interpret b.cache.state)) := by
            congr 1
            funext t
            apply ih
            exact (next_mass_le Q hL C R restartFuel hR.le c
              (materialize hL a.cache.state.data.remaining t)).trans_lt hfuel
          _ = (AdaptiveRounding.epochPMF (R : ℝ≥0) (interpret a.cache.state)).bind
              (fun e => FlexibleAdaptiveRounding.solve P (R : ℝ≥0) hR epochs e.state) := by
            rw [← RetainedTapeInput.scan_law Q hL C R a.cache, PMF.bind_map]
            rfl
          _ = _ := by rw [AdaptiveRounding.epochPMF, PMF.bind_map]; rfl

theorem execution_state_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (c : Cache H)
    (hfuel : (interpret c.state).mass < (R : ℝ≥0) ^ restartFuel) :
    (executionLaw Q hL C R restartFuel epochs c).map (fun x => interpret x.cache.state) =
      FlexibleAdaptiveRounding.solve P (R : ℝ≥0) hR epochs (interpret c.state) := by
  rw [executionLaw, PMF.map_comp]
  exact supplied_state_law Q hL C R restartFuel hR epochs c hfuel

theorem output_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (s : Code G D L)
    (hfuel : (interpret s).mass < (R : ℝ≥0) ^ restartFuel) :
    outputLaw Q hL C R restartFuel epochs s =
      FlexibleAdaptiveRounding.boundedOutput P (R : ℝ≥0) hR epochs (interpret s) := by
  unfold FlexibleAdaptiveRounding.boundedOutput
  have hs := supplied_state_law Q hL C R restartFuel hR epochs (refresh Q s) hfuel
  change _ = FlexibleAdaptiveRounding.solve P (R : ℝ≥0) hR epochs (interpret s) at hs
  rw [← hs, PMF.map_comp]
  rfl

theorem sampled_run_state_law (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (s : Code G D L)
    (hfuel : (interpret s).mass < (R : ℝ≥0) ^ restartFuel) :
    (sampledRunLaw Q hL C R restartFuel epochs s).map
        (fun d => interpret d.result.cache.state) =
      FlexibleAdaptiveRounding.solve P (R : ℝ≥0) hR epochs (interpret s) := by
  rw [sampledRunLaw, ← supplies_runSampled, PMF.map_comp]
  exact supplied_state_law Q hL C R restartFuel hR epochs (refresh Q s) hfuel

/-- Geometric outer fuel is sufficient for every supported actual supplied run. -/
theorem supplied_run_valid (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (s : Code G D L)
    (hrestart : (interpret s).mass < (R : ℝ≥0) ^ restartFuel)
    (hepochs : (interpret s).mass < (R : ℝ≥0) ^ epochs)
    {inputs : List (IntegerAdaptiveExecution.Input n L)}
    (hi : inputs ∈ (supplies Q hL C R restartFuel epochs (refresh Q s)).support) :
    IsIntegralCut G (cutSet (run Q hL C R restartFuel inputs s).cache.state.data.cut)
      (D : Set (Pair n)) := by
  apply FlexibleAdaptiveRounding.boundedOutput_valid P (R : ℝ≥0) hR epochs
    (interpret s) hepochs
  rw [← output_law Q hL C R restartFuel hR epochs s hrestart]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨inputs, hi, rfl⟩

theorem output_valid (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (s : Code G D L)
    (hrestart : (interpret s).mass < (R : ℝ≥0) ^ restartFuel)
    (hepochs : (interpret s).mass < (R : ℝ≥0) ^ epochs)
    {X : Finset (Fin n)} (hX : X ∈ (outputLaw Q hL C R restartFuel epochs s).support) :
    IsIntegralCut G X (D : Set (Pair n)) := by
  rw [output_law Q hL C R restartFuel hR epochs s hrestart] at hX
  exact FlexibleAdaptiveRounding.boundedOutput_valid P _ hR epochs (interpret s) hepochs hX

theorem sampled_run_valid (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel : ℕ) (hR : 1 < (R : ℝ≥0))
    (epochs : ℕ) (s : Code G D L)
    (hrestart : (interpret s).mass < (R : ℝ≥0) ^ restartFuel)
    (hepochs : (interpret s).mass < (R : ℝ≥0) ^ epochs)
    {d : RetainedSampledExecution.LoggedResult H}
    (hd : d ∈ (sampledRunLaw Q hL C R restartFuel epochs s).support) :
    IsIntegralCut G (cutSet d.result.cache.state.data.cut) (D : Set (Pair n)) := by
  apply output_valid Q hL C R restartFuel hR epochs s hrestart hepochs
  rw [← sampledRunLaw_output Q hL C R restartFuel epochs s]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨d, hd, rfl⟩

/-- Every supported supply consists of complete active permutations, has no
unused trailing epochs, and materializes at most the original label count. -/
theorem supplies_spec (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (c : Cache H)
    {inputs : List (IntegerAdaptiveExecution.Input n L)}
    (hi : inputs ∈ (supplies Q hL C R restartFuel epochs c).support) :
    inputs.length ≤ epochs ∧
      (∀ i ∈ inputs, i.order.length ≤ n * n) ∧
      CompleteInputs Q hL C R restartFuel inputs c := by
  induction epochs generalizing c inputs with
  | zero =>
      have he : inputs = [] := by simpa [supplies] using hi
      subst inputs
      simp [CompleteInputs]
  | succ epochs ih =>
      simp only [supplies] at hi
      split_ifs at hi with hz
      · have he : inputs = [] := by simpa using hi
        subst inputs
        simp [CompleteInputs]
      · obtain ⟨t, _, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hi
        obtain ⟨tail, htail, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
        subst inputs
        obtain ⟨hlen, horders, hcomplete⟩ := ih _ htail
        refine ⟨Nat.succ_le_succ hlen, ?_, ?_⟩
        · intro i hi
          rcases List.mem_cons.mp hi with he | hi
          · subst i
            rw [materialize_order_length]
            simpa only [Fintype.card_prod, Fintype.card_fin] using
              (remainingSet (stabilize Q R restartFuel c).cache.state.data.remaining).card_le_univ
          · exact horders i hi
        · simp only [CompleteInputs, ite_eq_right hz]
          exact ⟨materialize_order_nodup hL _ t, materialize_order_toFinset hL _ t,
            hcomplete⟩

theorem primitiveDraws_le {inputs : List (IntegerAdaptiveExecution.Input n L)}
    (h : ∀ i ∈ inputs, i.order.length ≤ n * n) :
    primitiveDraws inputs ≤ 2 * (n * n) * inputs.length := by
  induction inputs with
  | nil => simp [primitiveDraws]
  | cons i inputs ih =>
      have hi := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [primitiveDraws, List.length_cons]
      nlinarith

theorem supplies_draws_le (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs : ℕ) (c : Cache H)
    {inputs : List (IntegerAdaptiveExecution.Input n L)}
    (hi : inputs ∈ (supplies Q hL C R restartFuel epochs c).support) :
    primitiveDraws inputs ≤ 2 * (n * n) * epochs := by
  have hs := supplies_spec Q hL C R restartFuel epochs c hi
  exact (primitiveDraws_le hs.2.1).trans (Nat.mul_le_mul_left _ hs.1)

theorem scan_gates (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan Q hL C R M cells order c).work.gates = 0 := by
  induction order generalizing c with
  | nil => rfl
  | cons p ps ih =>
      simp only [scan]
      split_ifs <;> simp only [Work.add, refreshWork, Nat.zero_add, ih]

theorem stabilize_epochTests (Q : Optimizer H) (R restartFuel : ℕ) (c : Cache H) :
    (stabilize Q R restartFuel c).work.epochTests = 0 := by
  induction restartFuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      simp only [IntegerAdaptiveExecution.stabilize, Work.add, ih, Nat.add_zero]
      unfold IntegerAdaptiveExecution.advance
      split_ifs <;> rfl

theorem stabilize_massScans (Q : Optimizer H) (R restartFuel : ℕ) (c : Cache H) :
    (stabilize Q R restartFuel c).work.massScans =
      (stabilize Q R restartFuel c).work.restarts := by
  induction restartFuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
      simp only [IntegerAdaptiveExecution.stabilize, Work.add, ih]
      congr 1
      unfold IntegerAdaptiveExecution.advance
      split_ifs <;> rfl

theorem scan_massScans (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R M : ℕ) (cells : Pair n → Fin L) (order : List (Pair n)) (c : Cache H) :
    (scan Q hL C R M cells order c).work.massScans =
      2 * (scan Q hL C R M cells order c).work.rounds := by
  induction order generalizing c with
  | nil => rfl
  | cons p ps ih =>
      simp only [scan]
      split_ifs
      · simp only [Work.add, refreshWork, Nat.add_zero, ih]
        omega
      · rfl

theorem execute_massScans (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel : ℕ) (inputs : List (IntegerAdaptiveExecution.Input n L)) (c : Cache H) :
    (execute Q hL C R restartFuel inputs c).work.massScans =
      (execute Q hL C R restartFuel inputs c).work.restarts +
        2 * (execute Q hL C R restartFuel inputs c).work.rounds := by
  induction inputs generalizing c with
  | nil => simp [execute, stabilize_massScans, stabilize_rounds]
  | cons i inputs ih =>
      simp only [execute]
      split_ifs
      · simp [stabilize_massScans, stabilize_rounds]
      · simp only [Work.add, stabilize_massScans, scan_massScans, ih,
          scan_restarts, stabilize_rounds, Nat.zero_add]
        omega

theorem run_massScans (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel : ℕ) (inputs : List (IntegerAdaptiveExecution.Input n L)) (s : Code G D L) :
    (run Q hL C R restartFuel inputs s).work.massScans =
      1 + (run Q hL C R restartFuel inputs s).work.restarts +
        2 * (run Q hL C R restartFuel inputs s).work.rounds := by
  simp only [run, start, Work.add, refreshWork, Nat.zero_add, execute_massScans]
  omega

theorem execute_gates_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel : ℕ) (inputs : List (IntegerAdaptiveExecution.Input n L)) (c : Cache H) :
    (execute Q hL C R restartFuel inputs c).work.gates ≤
      (inputs.length + 1) * restartFuel := by
  induction inputs generalizing c with
  | nil => simp [execute, stabilize_gates]
  | cons i inputs ih =>
      simp only [execute]
      split_ifs
      · rw [stabilize_gates]
        exact Nat.le_mul_of_pos_left _ (by omega)
      · simp only [Work.add, stabilize_gates, scan_gates, Nat.zero_add]
        have ht := ih (scan Q hL C R (stabilize Q R restartFuel c).cache.state.data.current
          i.cell i.order (stabilize Q R restartFuel c).cache).cache
        simp only [List.length_cons]
        nlinarith

theorem execute_epochTests_le (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel : ℕ) (inputs : List (IntegerAdaptiveExecution.Input n L)) (c : Cache H)
    (h : ∀ i ∈ inputs, i.order.length ≤ n * n) :
    (execute Q hL C R restartFuel inputs c).work.epochTests ≤ n * n * inputs.length := by
  induction inputs generalizing c with
  | nil => simp [execute, stabilize_epochTests]
  | cons i inputs ih =>
      simp only [execute]
      split_ifs
      · simp [stabilize_epochTests]
      · have hi := (scan_tests_le Q hL C R
          (stabilize Q R restartFuel c).cache.state.data.current i.cell i.order
          (stabilize Q R restartFuel c).cache).trans (h i (by simp))
        have ht := ih (scan Q hL C R (stabilize Q R restartFuel c).cache.state.data.current
          i.cell i.order (stabilize Q R restartFuel c).cache).cache
          (fun j hj => h j (by simp [hj]))
        simp only [Work.add, stabilize_epochTests, Nat.zero_add, List.length_cons]
        nlinarith

/-- Actual counters, including the initial optimizer call. These count calls
and control events; they do not assert machine or random-bit complexity. -/
theorem supplied_run_work_bounds (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs J : ℕ) (hR : 1 < (R : ℝ≥0))
    (s : Code G D L) (hJ : (interpret s).mass < (R : ℝ≥0) ^ (J + 1))
    {inputs : List (IntegerAdaptiveExecution.Input n L)}
    (hi : inputs ∈ (supplies Q hL C R restartFuel epochs (refresh Q s)).support) :
    let w := (run Q hL C R restartFuel inputs s).work
    inputs.length ≤ epochs ∧ primitiveDraws inputs ≤ 2 * (n * n) * epochs ∧
      w.rounds ≤ (remainingSet s.data.remaining).card ∧ w.restarts ≤ J ∧
      w.families = 1 + w.restarts + w.rounds ∧
      w.candidates ≤ n * n * (1 + J + (remainingSet s.data.remaining).card) ∧
      w.gates ≤ (epochs + 1) * restartFuel ∧ w.epochTests ≤ n * n * epochs := by
  have hs := supplies_spec Q hL C R restartFuel epochs (refresh Q s) hi
  have hround := execute_rounds_le Q hL C R restartFuel inputs (refresh Q s)
  change (execute Q hL C R restartFuel inputs (refresh Q s)).work.rounds ≤
    (remainingSet s.data.remaining).card at hround
  have hrestart := execute_restarts_le Q hL C R restartFuel J hR inputs (refresh Q s) hJ
  have hfamily := run_families Q hL C R restartFuel inputs s
  have hcandidate := run_candidates_le Q hL C R restartFuel inputs s
  have hgate := execute_gates_le Q hL C R restartFuel inputs (refresh Q s)
  have htest := execute_epochTests_le Q hL C R restartFuel inputs (refresh Q s) hs.2.1
  have hdraw := supplies_draws_le Q hL C R restartFuel epochs (refresh Q s) hi
  simp only [run, start, Work.add, refreshWork, Nat.zero_add] at hfamily hcandidate ⊢
  refine ⟨hs.1, hdraw, hround, hrestart, hfamily, ?_, ?_, ?_⟩
  · apply hcandidate.trans
    apply Nat.mul_le_mul_left
    omega
  · exact hgate.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hs.1 1))
  · exact htest.trans (Nat.mul_le_mul_left _ hs.1)

/-- These bounds apply to the counters returned by the actual single-pass
sampler/controller, with no optimizer replay charged or omitted. -/
theorem sampled_run_work_bounds (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs J : ℕ) (hR : 1 < (R : ℝ≥0))
    (s : Code G D L) (hJ : (interpret s).mass < (R : ℝ≥0) ^ (J + 1))
    {d : RetainedSampledExecution.LoggedResult H}
    (hd : d ∈ (sampledRunLaw Q hL C R restartFuel epochs s).support) :
    let w := d.result.work
    d.inputs.length ≤ epochs ∧ primitiveDraws d.inputs ≤ 2 * (n * n) * epochs ∧
      w.rounds ≤ (remainingSet s.data.remaining).card ∧ w.restarts ≤ J ∧
      w.families = 1 + w.restarts + w.rounds ∧
      w.candidates ≤ n * n * (1 + J + (remainingSet s.data.remaining).card) ∧
      w.gates ≤ (epochs + 1) * restartFuel ∧ w.epochTests ≤ n * n * epochs := by
  rw [sampledRunLaw, ← supplies_runSampled] at hd
  obtain ⟨inputs, hi, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  exact supplied_run_work_bounds Q hL C R restartFuel epochs J hR s hJ hi

theorem sampled_run_control_bound (Q : Optimizer H) (hL : 0 < L) [NeZero L]
    (C : CutOracle G L hL) (R restartFuel epochs J : ℕ) (hR : 1 < (R : ℝ≥0))
    (s : Code G D L) (hJ : (interpret s).mass < (R : ℝ≥0) ^ (J + 1))
    {d : RetainedSampledExecution.LoggedResult H}
    (hd : d ∈ (sampledRunLaw Q hL C R restartFuel epochs s).support) :
    d.result.work.massScans = 1 + d.result.work.restarts + 2 * d.result.work.rounds ∧
      d.result.work.control ≤ (epochs + 1) * restartFuel + n * n * epochs +
        3 * (remainingSet s.data.remaining).card + 2 * J + 1 := by
  have hb := sampled_run_work_bounds Q hL C R restartFuel epochs J hR s hJ hd
  rw [sampledRunLaw, ← supplies_runSampled] at hd
  obtain ⟨inputs, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  have hm := run_massScans Q hL C R restartFuel inputs s
  refine ⟨hm, ?_⟩
  dsimp only at hb ⊢
  unfold Work.control
  omega

end
end DirectedFlowCutGap.RetainedExecutionLaw
