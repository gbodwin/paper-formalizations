import DirectedFlowCutGap.FinitePermutationSampler
import DirectedFlowCutGap.GridLevelSampling
import DirectedFlowCutGap.AdaptiveRounding

/-!
# A concrete exact finite sampler for an epoch

Independent primitive draws generate the permutation tape and one grid-cell
index per label. A computable supplied enumeration connects these tapes to the
caller. Their map through midpoint cuts is exactly the existing joint epoch
PMF, not merely the same marginals. The cut operation here is the mathematical
specification; the integer shortest-path implementation refines it separately.

A fair-bit realization remains a separate obligation: unbounded rejection can
be exact in expected time; a fixed cutoff has a failure outcome and a different
law. None of the theorems below identify a truncated rejection law with this
primitive law or claim a complete bit-complexity bound.
-/
namespace DirectedFlowCutGap.FiniteGridSampler

open FinitePermutationSampler
open MeasureTheory
open scoped BigOperators NNReal ENNReal

/-- A concrete ordered tape of `n` cell indices. -/
def Cells (L : ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin L × Cells L n

instance cellsFintype (L : ℕ) : (n : ℕ) → Fintype (Cells L n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (Fin L) (Cells L n) inferInstance (cellsFintype L n)

instance cellsNonempty (L : ℕ) [NeZero L] : (n : ℕ) → Nonempty (Cells L n)
  | 0 => ⟨()⟩
  | n + 1 => ⟨(0, Classical.choice (cellsNonempty L n))⟩

/-- Decoding cells is explicit recursion, not a choice of a finite enumeration. -/
def cellsDecode (L : ℕ) : (n : ℕ) → Cells L n ≃ (Fin n → Fin L)
  | 0 =>
      { toFun := fun _ => Fin.elim0
        invFun := fun _ => ()
        left_inv := by intro t; cases t; rfl
        right_inv := by intro f; funext i; exact Fin.elim0 i }
  | n + 1 =>
      { toFun := fun t => Fin.cons t.1 (cellsDecode L n t.2)
        invFun := fun f => (f 0, (cellsDecode L n).symm (fun i => f i.succ))
        left_inv := by
          intro t
          rcases t with ⟨j, t⟩
          simp
          rfl
        right_inv := by
          intro f
          funext i
          refine Fin.cases ?_ (fun i => ?_) i <;> simp }

/-- A list interpreter that records the number of cell draws consumed. -/
def cellsRun (L : ℕ) : (n : ℕ) → Cells L n → List (Fin L) × ℕ
  | 0, _ => ([], 0)
  | n + 1, (j, t) =>
      let r := cellsRun L n t
      (j :: r.1, r.2 + 1)

theorem cellsRun_list (L n : ℕ) (t : Cells L n) :
    (cellsRun L n t).1 = List.ofFn (cellsDecode L n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases t with ⟨j, t⟩
      change j :: (cellsRun L n t).1 = List.ofFn (Fin.cons j (cellsDecode L n t))
      rw [List.ofFn_succ, ih]
      rfl

@[simp] theorem cellsRun_draws (L n : ℕ) (t : Cells L n) :
    (cellsRun L n t).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rcases t with ⟨j, t⟩; simp [cellsRun, ih]

/-- Relabel the explicitly sampled cells by the caller's enumeration. -/
def labelCells {E : Type*} {n L : ℕ} (enum : Fin n ≃ E) : Cells L n ≃ (E → Fin L) :=
  (cellsDecode L n).trans (Equiv.arrowCongr enum (Equiv.refl _))

/-- Exact random input expected by an epoch: a permutation and independent cells. -/
abbrev Input (E : Type*) (L : ℕ) := Equiv.Perm E × (E → Fin L)

/-- Both tapes decode by a computable bijection. -/
def decodeInput {E : Type*} {n L : ℕ} (enum : Fin n ≃ E) :
    (Tape n × Cells L n) ≃ Input E L :=
  Equiv.prodCongr (labelPermutation enum) (labelCells enum)

/-- An analysis reference enumeration changes only the permutation coordinate;
the executed order and the label-indexed cells still use the supplied `enum`. -/
def decodeRelativeInput {E : Type*} {n L : ℕ} (enum reference : Fin n ≃ E) :
    (Tape n × Cells L n) ≃ Input E L :=
  Equiv.prodCongr (relativePermutation enum reference) (labelCells enum)

/-- The concrete finite sample output, with its counters from the same run.
Cells are stored in supplied-enumeration order, independently of sampled order. -/
@[ext] structure SampleRun (E : Type*) (L : ℕ) where
  order : List E
  cells : List (Fin L)
  draws : ℕ
  scans : ℕ

/-- Shared finite list interpreter for one complete permutation/cell sample. -/
def runInput {E : Type*} {n L : ℕ} (enum : Fin n ≃ E)
    (t : Tape n × Cells L n) : SampleRun E L :=
  let p := labelRun enum t.1
  let c := cellsRun L n t.2
  ⟨p.order, c.1, p.draws + c.2, p.scans⟩

@[simp] theorem runInput_order {E : Type*} {n L : ℕ} (enum : Fin n ≃ E)
    (t : Tape n × Cells L n) : (runInput enum t).order = labelOrder enum t.1 := rfl

theorem runInput_cells {E : Type*} {n L : ℕ} (enum : Fin n ≃ E)
    (t : Tape n × Cells L n) :
    (runInput enum t).cells = List.ofFn (fun i => (decodeInput enum t).2 (enum i)) := by
  simp [runInput, cellsRun_list, decodeInput, labelCells, Equiv.arrowCongr]

@[simp] theorem runInput_draws {E : Type*} {n L : ℕ} (enum : Fin n ≃ E)
    (t : Tape n × Cells L n) : (runInput enum t).draws = 2 * n := by
  simp [runInput]; omega

@[simp] theorem runInput_scans {E : Type*} {n L : ℕ} (enum : Fin n ≃ E)
    (t : Tape n × Cells L n) : (runInput enum t).scans = scanBudget n + n :=
  labelScans_eq enum t.1

/-- The instrumented finite execution consumes `2n` primitive draws. -/
def primitiveDraws {n L : ℕ} (t : Tape n × Cells L n) : ℕ :=
  (run n t.1).draws + (cellsRun L n t.2).2

@[simp] theorem primitiveDraws_eq {n L : ℕ} (t : Tape n × Cells L n) :
    primitiveDraws t = 2 * n := by simp [primitiveDraws]; omega

noncomputable section

/-- The literal independent cell-draw recursion. -/
def cellsPMF (L : ℕ) [NeZero L] : (n : ℕ) → PMF (Cells L n)
  | 0 => PMF.pure ()
  | n + 1 => independent (PMF.uniformOfFintype (Fin L)) (cellsPMF L n)

theorem cellsPMF_uniform (L : ℕ) [NeZero L] (n : ℕ) :
    cellsPMF L n = PMF.uniformOfFintype (Cells L n) := by
  induction n with
  | zero =>
      apply PMF.ext
      intro t
      cases t
      change (PMF.pure () : PMF Unit) () = (PMF.uniformOfFintype Unit) ()
      simp [PMF.uniformOfFintype_apply]
  | succ n ih => rw [cellsPMF, ih]; exact independent_uniform

/-- One epoch's actual primitive input law, before cuts are computed. -/
def tapePMF (n L : ℕ) [NeZero L] : PMF (Tape n × Cells L n) :=
  independent (FinitePermutationSampler.tapePMF n) (cellsPMF L n)

theorem tapePMF_uniform (n L : ℕ) [NeZero L] :
    tapePMF n L = PMF.uniformOfFintype (Tape n × Cells L n) := by
  rw [tapePMF, FinitePermutationSampler.tapePMF_uniform, cellsPMF_uniform]
  exact independent_uniform

/-- Exact joint uniform input law, establishing permutation/cell independence. -/
theorem input_law {E : Type*} [Fintype E] [DecidableEq E] {n L : ℕ} [NeZero L] (enum : Fin n ≃ E) :
    (tapePMF n L).map (decodeInput enum) = PMF.uniformOfFintype (Input E L) := by
  rw [tapePMF_uniform]
  exact uniform_map_equiv (decodeInput enum)

/-- The materialized finite lists have exactly the decoded input law, with
the execution counters retained in the same output. -/
theorem runInput_law {E : Type*} [Fintype E] [DecidableEq E]
    {n L : ℕ} [NeZero L] (enum : Fin n ≃ E) :
    (tapePMF n L).map (runInput enum) =
      (PMF.uniformOfFintype (Input E L)).map (fun ω =>
        (⟨List.ofFn (fun i => ω.1 (enum i)), List.ofFn (fun i => ω.2 (enum i)),
          2 * n, scanBudget n + n⟩ : SampleRun E L)) := by
  rw [← input_law enum, PMF.map_comp]
  congr 1
  funext t
  apply SampleRun.ext
  · exact labelOrder_eq enum t.1
  · exact runInput_cells enum t
  · exact runInput_draws enum t
  · exact runInput_scans enum t

/-- Exact uniformity also holds relative to a separate analysis enumeration. -/
theorem relative_input_law {E : Type*} [Fintype E] [DecidableEq E]
    {n L : ℕ} [NeZero L] (enum reference : Fin n ≃ E) :
    (tapePMF n L).map (decodeRelativeInput enum reference) =
      PMF.uniformOfFintype (Input E L) := by
  rw [tapePMF_uniform]
  exact uniform_map_equiv (decodeRelativeInput enum reference)

local instance finMeasurableSpace (L : ℕ) : MeasurableSpace (Fin L) := ⊤
local instance permMeasurableSpace (E : Type*) : MeasurableSpace (Equiv.Perm E) := ⊤

/-- Uniform finite functions really have independent uniform coordinates. -/
theorem uniform_function_measure {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    (PMF.uniformOfFintype (I → A)).toMeasure =
      Measure.pi (fun _ : I => (PMF.uniformOfFintype A).toMeasure) := by
  apply Measure.ext_of_singleton
  intro f
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.pi_singleton]
  have hu (a : A) : (PMF.uniformOfFintype A).toMeasure {a} =
      (Fintype.card A : ℝ≥0∞)⁻¹ := FrozenEpochProbability.finiteUniform_singleton a
  simp_rw [hu]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Nat.cast_pow,
    Finset.prod_const, Finset.card_univ, ENNReal.inv_pow]

/-- Uniform finite pairs have their product measure, with all normalizations. -/
theorem uniform_pair_measure {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] :
    (PMF.uniformOfFintype (A × B)).toMeasure =
      (PMF.uniformOfFintype A).toMeasure.prod (PMF.uniformOfFintype B).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [show (PMF.uniformOfFintype A).toMeasure {a} = (Fintype.card A : ℝ≥0∞)⁻¹ from
      FrozenEpochProbability.finiteUniform_singleton a,
    show (PMF.uniformOfFintype B).toMeasure {b} = (Fintype.card B : ℝ≥0∞)⁻¹ from
      FrozenEpochProbability.finiteUniform_singleton b]
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod, ENNReal.mul_inv]

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Midpoint cut specification for a concrete finite grid sample. -/
def draw (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V) {L : ℕ}
    (ω : Input E L) : AdaptiveRounding.Sample E V :=
  (ω.1, fun e => FiniteCutLaw.draw G (w e) (s e) (GridLevelSampling.midpoint L (ω.2 e)))

/-- The finite cell law maps to the exact product of the original cut laws. -/
theorem draw_uniform_eq_samplePMF (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (L : ℕ) [NeZero L] (hw : ∀ e, GridLevelSampling.OnGrid L (w e)) :
    (PMF.uniformOfFintype (Input E L)).map (draw G w s) =
      AdaptiveRounding.samplePMF G w s := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hcut (e : E) :
      (PMF.uniformOfFintype (Fin L)).toMeasure.map
        (fun j => FiniteCutLaw.draw G (w e) (s e) (GridLevelSampling.midpoint L j)) =
      FiniteCutLaw.cutMeasure G (w e) (s e) := by
    rw [PMF.toMeasure_map
      (fun j : Fin L => FiniteCutLaw.draw G (w e) (s e) (GridLevelSampling.midpoint L j))
      (PMF.uniformOfFintype (Fin L)) (measurable_of_finite _)]
    exact GridLevelSampling.gridCutPMF_toMeasure G (w e) (s e) L hL (hw e)
  have hc : (PMF.uniformOfFintype (E → Fin L)).toMeasure.map
      (fun c e => FiniteCutLaw.draw G (w e) (s e) (GridLevelSampling.midpoint L (c e))) =
      Measure.pi (fun e => FiniteCutLaw.cutMeasure G (w e) (s e)) := by
    rw [uniform_function_measure]
    have hp := Measure.pi_map_pi
      (μ := fun _ : E => (PMF.uniformOfFintype (Fin L)).toMeasure)
      (f := fun e j => FiniteCutLaw.draw G (w e) (s e) (GridLevelSampling.midpoint L j))
      (fun _ => (measurable_of_finite _).aemeasurable)
    exact hp.trans (by simp_rw [hcut])
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (draw G w s) (PMF.uniformOfFintype (Input E L))
      (measurable_of_finite _), AdaptiveRounding.samplePMF_toMeasure,
    uniform_pair_measure]
  rw [show (draw G w s : Input E L → AdaptiveRounding.Sample E V) =
    Prod.map (id : Equiv.Perm E → Equiv.Perm E)
      (fun c : E → Fin L => fun e : E =>
        FiniteCutLaw.draw G (w e) (s e) (GridLevelSampling.midpoint L (c e))) from rfl]
  rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_finite _), Measure.map_id, hc]
  rfl

/-- Concrete tapes, permutation interpreter and grid cuts realize exactly the
finite joint law used by the epoch analysis. -/
theorem epoch_sample_law (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    {n L : ℕ} [NeZero L] (enum : Fin n ≃ E)
    (hw : ∀ e, GridLevelSampling.OnGrid L (w e)) :
    (tapePMF n L).map (fun t => draw G w s (decodeInput enum t)) =
      AdaptiveRounding.samplePMF G w s := by
  calc
    _ = ((tapePMF n L).map (decodeInput enum)).map (draw G w s) :=
      (PMF.map_comp (decodeInput enum) (tapePMF n L) (draw G w s)).symm
    _ = _ := by
      rw [input_law enum]
      exact draw_uniform_eq_samplePMF G w s L hw

/-- The sample law remains exact for the reference enumeration used by the
existing adaptive analysis. No runtime call to that enumeration is introduced. -/
theorem relative_epoch_sample_law (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    {n L : ℕ} [NeZero L] (enum reference : Fin n ≃ E)
    (hw : ∀ e, GridLevelSampling.OnGrid L (w e)) :
    (tapePMF n L).map (fun t => draw G w s (decodeRelativeInput enum reference t)) =
      AdaptiveRounding.samplePMF G w s := by
  calc
    _ = ((tapePMF n L).map (decodeRelativeInput enum reference)).map (draw G w s) :=
      (PMF.map_comp (decodeRelativeInput enum reference) (tapePMF n L) (draw G w s)).symm
    _ = _ := by
      rw [relative_input_law enum reference]
      exact draw_uniform_eq_samplePMF G w s L hw

/-- Every deterministic epoch interpreter inherits the same exact outcome law.
Pointwise refinement can be supplied by the integer retained-state execution. -/
theorem interpreted_epoch_law {A : Type*} (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) {n L : ℕ} [NeZero L] (enum : Fin n ≃ E)
    (hw : ∀ e, GridLevelSampling.OnGrid L (w e))
    (spec : AdaptiveRounding.Sample E V → A) (impl : Tape n × Cells L n → A)
    (hrefines : ∀ t, impl t = spec (draw G w s (decodeInput enum t))) :
    (tapePMF n L).map impl = (AdaptiveRounding.samplePMF G w s).map spec := by
  rw [← epoch_sample_law G w s enum hw, PMF.map_comp]
  congr 1
  funext t
  exact hrefines t

/-- All midpoint images have positive probability under the original joint law. -/
theorem draw_mem_support (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    {L : ℕ} [NeZero L] (hw : ∀ e, GridLevelSampling.OnGrid L (w e))
    (ω : Input E L) : draw G w s ω ∈ (AdaptiveRounding.samplePMF G w s).support := by
  rw [← draw_uniform_eq_samplePMF G w s L hw]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨ω, PMF.mem_support_uniformOfFintype ω, rfl⟩

section EpochInterpreter
open CandidateSchedule CandidateSchedule.State AdaptiveEpoch AdaptiveRounding
variable {G : Digraph V} {D : Finset (V × V)} {K : ℝ≥0}

/-- Epoch control depends on levels only through their actual cuts. -/
theorem run_eq_of_cut_eq (r M : ℝ≥0) (u v : (V × V) → UnitLevel)
    (S : State G D K) (order : List (V × V))
    (hcut : ∀ p, levelCut G (S.weight p) p.1 (u p).val =
      levelCut G (S.weight p) p.1 (v p).val) :
    AdaptiveEpoch.run r M u S order = AdaptiveEpoch.run r M v S order := by
  induction order generalizing S with
  | nil => rfl
  | cons p ps ih =>
      simp only [AdaptiveEpoch.run]
      split_ifs with h
      · have hr : S.round p h.2 (u p).val (u p).property =
            S.round p h.2 (v p).val (v p).property := by
          unfold State.round
          congr 1
          exact congrArg (fun X => S.cut ∪ X) (hcut p)
        rw [hr]
        rw [ih (S.round p h.2 (v p).val (v p).property) (fun q => hcut q)]
      · rfl

/-- A genuine closed-unit midpoint for every positive grid size. -/
def midpointUnit (L : ℕ) [NeZero L] (j : Fin L) : UnitLevel :=
  ⟨(GridLevelSampling.midpoint L j).toNNReal, by
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have h := GridLevelSampling.cell_subset_unit hL j (GridLevelSampling.midpoint_mem_cell hL j)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h.1]
    exact h.2⟩

/-- Active labels use their sampled cells; unused original labels receive zero. -/
def midpointLevels (S : State G D K) {L : ℕ} [NeZero L]
    (cells : Label S → Fin L) : (V × V) → UnitLevel :=
  fun p => if hp : p ∈ S.remaining then midpointUnit L (cells ⟨p, hp⟩) else ⟨0, zero_le⟩

/-- Midpoint levels and the finite law's chosen representatives give identical
actual cuts, including labels outside the frozen remaining set. -/
theorem midpointLevels_cut (S : State G D K) {L : ℕ} [NeZero L]
    (hw : ∀ p : Label S, GridLevelSampling.OnGrid L (S.weight p.val))
    (ω : Input (Label S) L) (p : V × V) :
    levelCut G (S.weight p) p.1 (midpointLevels S ω.2 p).val =
      levelCut G (S.weight p) p.1
        (sampleLevels S (draw G (fun q : Label S => S.weight q.val) (fun q => q.val.1) ω) p).val := by
  classical
  by_cases hp : p ∈ S.remaining
  · have h := sampleLevels_cut S
      (draw_mem_support G (fun q : Label S => S.weight q.val) (fun q => q.val.1) hw ω) ⟨p, hp⟩
    rw [h]
    simp [midpointLevels, hp, midpointUnit, draw, FiniteCutLaw.draw]
  · simp [midpointLevels, sampleLevels, hp]

omit [Fintype V] in
/-- Exact agreement of the executed order with the analysis's permutation
coordinate; the reference enumeration is used only in this proof bridge. -/
theorem sampleOrder_relative (S : State G D K)
    (enum : Fin (Fintype.card (Label S)) ≃ Label S)
    (t : Tape (Fintype.card (Label S))) :
    sampleOrder S (relativePermutation enum (Fintype.equivFin (Label S)).symm t) =
      (labelOrder enum t).map Subtype.val := by
  rw [labelOrder_relative enum (Fintype.equivFin (Label S)).symm]
  simp only [sampleOrder, List.map_ofFn, Function.comp_def]

/-- Concrete finite samples interpreted by the original deterministic epoch:
computed order, actual midpoint levels, and no favorable random choice. -/
def midpointTapeEpoch (r : ℝ≥0) (S : State G D K) {L : ℕ} [NeZero L]
    (enum : Fin (Fintype.card (Label S)) ≃ Label S)
    (t : Tape (Fintype.card (Label S)) × Cells L (Fintype.card (Label S))) : Result G D K :=
  AdaptiveEpoch.run r S.mass (midpointLevels S (labelCells enum t.2)) S
    ((labelOrder enum t.1).map Subtype.val)

/-- Pointwise representative replacement and order alignment, before any
probability argument or stopping-time manipulation. -/
theorem midpointTapeEpoch_eq (r : ℝ≥0) (S : State G D K) {L : ℕ} [NeZero L]
    (enum : Fin (Fintype.card (Label S)) ≃ Label S)
    (hw : ∀ p : Label S, GridLevelSampling.OnGrid L (S.weight p.val))
    (t : Tape (Fintype.card (Label S)) × Cells L (Fintype.card (Label S))) :
    midpointTapeEpoch r S enum t = epoch r S
      (draw G (fun p : Label S => S.weight p.val) (fun p => p.val.1)
        (decodeRelativeInput enum (Fintype.equivFin (Label S)).symm t)) := by
  unfold midpointTapeEpoch epoch
  rw [show (draw G (fun p : Label S => S.weight p.val) (fun p => p.val.1)
      (decodeRelativeInput enum (Fintype.equivFin (Label S)).symm t)).1 =
      relativePermutation enum (Fintype.equivFin (Label S)).symm t.1 from rfl,
    sampleOrder_relative]
  exact run_eq_of_cut_eq r S.mass _ _ S _
    (midpointLevels_cut S hw (decodeRelativeInput enum (Fintype.equivFin (Label S)).symm t))

/-- The actual finite tape/midpoint experiment realizes the very same stopped
one-epoch law used by the existing adaptive analysis. -/
theorem midpointTapeEpoch_law (r : ℝ≥0) (S : State G D K) {L : ℕ} [NeZero L]
    (enum : Fin (Fintype.card (Label S)) ≃ Label S)
    (hw : ∀ p : Label S, GridLevelSampling.OnGrid L (S.weight p.val)) :
    (tapePMF (Fintype.card (Label S)) L).map (midpointTapeEpoch r S enum) = epochPMF r S := by
  unfold epochPMF
  rw [← relative_epoch_sample_law G (fun p : Label S => S.weight p.val) (fun p => p.val.1)
    enum (Fintype.equivFin (Label S)).symm hw, PMF.map_comp]
  congr 1
  funext t
  exact midpointTapeEpoch_eq r S enum hw t

end EpochInterpreter

end
end DirectedFlowCutGap.FiniteGridSampler
