import DirectedFlowCutGap.EncodedRoundingInput
import DirectedFlowCutGap.RetainedTapeInput

/-!
# Charged materialization of the adaptive finite tape

The finite tape is input data here; no uniform draw or random bit is free.
This program computes the permutation once and binds the concrete active-label
equivalence once. Its forward map is a bounded List.get and its inverse map is
a bounded List.idxOf on the retained active list. Cell decoding walks the input
tape, so every cell lookup pays for that walk as well as the inverse lookup.

The active dictionary build charge includes the row-major universe, mask
filter, length/cardinality reads, and retained equivalence constructors. The
quadratic copy allowance is intentionally conservative. No arbitrary caller
function is assigned a constant unit cost. Ghost counters are excluded.
-/
namespace DirectedFlowCutGap.EncodedTapeMaterialization

-- Unfold equal finite-cardinality encodings during dependent tactic matching.
set_option backward.isDefEq.respectTransparency false
open RetainedGridState EncodedRoundingInput RetainedTapeInput
open FinitePermutationSampler

variable {n L : ℕ}

/-- Concrete forward lookups in the one retained active equivalence. -/
def enumerate (a : PairFlags n) (enum : Fin (Fintype.card ↥(remainingSet a)) ≃ ↥(remainingSet a)) :
    List (Fin (Fintype.card ↥(remainingSet a))) → List (Pair n) × ℕ
  | [] => ([],1)
  | i::is =>
      let r := enumerate a enum is
      ((enum i).val::r.1,r.2+8*(n*n+1))

theorem enumerate_value (a : PairFlags n)
    (enum : Fin (Fintype.card ↥(remainingSet a)) ≃ ↥(remainingSet a))
    (is : List (Fin (Fintype.card ↥(remainingSet a)))) :
    (enumerate a enum is).1 = is.map (fun i => (enum i).val) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [enumerate,List.map_cons,ih]

theorem enumerate_work (a : PairFlags n)
    (enum : Fin (Fintype.card ↥(remainingSet a)) ≃ ↥(remainingSet a))
    (is : List (Fin (Fintype.card ↥(remainingSet a)))) :
    (enumerate a enum is).2 = 8*(n*n+1)*is.length+1 := by
  induction is with
  | nil => simp [enumerate]
  | cons i is ih => simp only [enumerate,List.length_cons,ih]; ring

def activeCount (a : PairFlags n) : ℕ := Fintype.card ↥(remainingSet a)

theorem activeCount_le (a : PairFlags n) : activeCount a ≤ n*n := by
  simpa only [activeCount,Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using
    (remainingSet a).card_le_univ

/-- The declared dictionary cost includes universe and mask construction. -/
def dictionaryBound (n : ℕ) : ℕ := 32*(n*n+1)^2

/-- The sampled permutation is evaluated exactly once. The order map and cell
array read only the retained equivalence and this retained permutation result. -/
def materialize (hL : 0<L) (a : PairFlags n) (t : RetainedTapeInput.Tape L a) :
    IntegerAdaptiveExecution.Input n L × ℕ :=
  let enum := activeEnum a
  let p := FinitePermutationSampler.run (activeCount a) t.1
  let o := enumerate a enum p.order
  let c := tabulate fun u : Fin n => tabulate fun v : Fin n =>
    if hp : flag a (u,v) = true then
      (FiniteGridSampler.labelCells enum t.2 ⟨(u,v),(mem_remainingSet a (u,v)).mpr hp⟩,
        16*(n*n+1))
    else (⟨0,hL⟩,4)
  (⟨o.1,c.1⟩,dictionaryBound n+16*(p.scans+p.draws+1)+o.2+c.2+8)

theorem materialize_value (hL : 0<L) (a : PairFlags n) (t : RetainedTapeInput.Tape L a) :
    (materialize hL a t).1 = RetainedTapeInput.materialize hL a t := by
  apply congrArg₂ IntegerAdaptiveExecution.Input.mk
  · simp only [enumerate_value,labelOrder,
      labelRun,FinitePermutationSampler.enumerate_list,List.map_map]
    rfl
  · apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp only [tabulate_value,Vector.getElem_ofFn]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact (h₂ ((mem_remainingSet a _).mpr h₁)).elim
    · exact (h₁ ((mem_remainingSet a _).mp h₂)).elim
    · rfl

def materializationBound (n : ℕ) : ℕ :=
  dictionaryBound n+16*((n*n)^2+n*n+1)+8*(n*n+1)*(n*n)+1+
    n*(n*(16*(n*n+1))+arrayBound n)+arrayBound n+8

theorem materialize_bound (hL : 0<L) (a : PairFlags n) (t : RetainedTapeInput.Tape L a) :
    (materialize hL a t).2 ≤ materializationBound n := by
  have hm := activeCount_le a
  have hp := scanBudget_le_square (activeCount a)
  have ho := enumerate_work a (activeEnum a)
    (FinitePermutationSampler.run (activeCount a) t.1).order
  rw [run_length] at ho
  have hc := tabulate_bound (fun u : Fin n => tabulate fun v : Fin n =>
    if hp : flag a (u,v) = true then
      (FiniteGridSampler.labelCells (activeEnum a) t.2
        ⟨(u,v),(mem_remainingSet a (u,v)).mpr hp⟩,16*(n*n+1))
    else (⟨0,hL⟩,4)) (n*(16*(n*n+1))+arrayBound n) (by
      intro u
      apply tabulate_bound
      intro v
      split <;> dsimp only <;> omega)
  have hp' : scanBudget (activeCount a) ≤ (n*n)^2 := hp.trans (by nlinarith)
  simp only [materialize,run_scans,run_draws]
  unfold materializationBound
  nlinarith

/-- Finite-tape interpretation has exactly the original input, so all joint
permutation/cell laws and every selected control branch are preserved. -/
theorem materialize_order (hL : 0<L) (a : PairFlags n) (t : RetainedTapeInput.Tape L a) :
    (materialize hL a t).1.order = (RetainedTapeInput.materialize hL a t).order := by
  rw [materialize_value]

end DirectedFlowCutGap.EncodedTapeMaterialization
