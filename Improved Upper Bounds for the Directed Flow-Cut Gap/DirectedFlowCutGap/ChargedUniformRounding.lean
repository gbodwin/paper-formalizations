import DirectedFlowCutGap.PreparedIntegerController
import DirectedFlowCutGap.EncodedUniformRounding

/-!
# Composition of the uniform-weight word charges

The dispatcher observes the existing parameter, chain, and projection
charges and runs the prepared integer controller on the materialized
chain. Its charge includes the demand mask, dictionary and initial state.
Erasing the charges preserves the fair-bit tree.
-/

namespace DirectedFlowCutGap.ChargedUniformRounding

open scoped NNReal
open FiniteDrawTrees LazyFairBitTrees RetainedGridState
open EncodedUnitCostReplication EncodedUniformWeightParameters EncodedUniformChain
open EncodedUniformOutput RawNonnegativeRational

theorem map_lower {A B : Type} (T : ℕ) (f : A → B) (t : FiniteDrawTrees.Tree A) :
    f <$> lower T t = lower T (f <$> t) := by
  induction t with
  | pure a => rfl
  | draw n hn next ih =>
    change f <$> (rejection n hn T >>= fun r => lower T (next r.value)) =
      rejection n hn T >>= fun r => lower T (f <$> next r.value)
    simp only [map_bind, ih]

def bitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (Flags n × ℕ) :=
  let p := compute D
  if h : Code.one.le p.total = true then
    let chain := materialize p.ports p.average p.counts
    map (fun (mask, paid) =>
      let result := originalMaskWithCost chain mask
      (result.1, p.work + chain.work + paid + result.2 + 10))
      (PreparedIntegerController.bitTree T chain.data.adjacency chain.cutoff (expand_cutoff_bounds D h).1)
  else .pure (Vector.replicate n false, p.work + 4 * n + 10)

theorem bitTree_value {n : ℕ} (T : ℕ) (D : Input n) :
    map Prod.fst (bitTree T D) = EncodedUniformRounding.bitTree T D := by
  unfold bitTree EncodedUniformRounding.bitTree EncodedUniformRounding.tree
  dsimp only
  split_ifs with h
  · let chain := expand D
    let ht := (expand_cutoff_bounds D h).1
    let t := PreparedIntegerController.bitTree T chain.data.adjacency chain.cutoff ht
    let p := EncodedIntegerRounding.tree chain.data.adjacency chain.cutoff ht
    have hplain : Prod.fst <$> t = lower T p := PreparedIntegerController.bitTree_value ..
    change Prod.fst <$> ((fun a =>
      ((originalMaskWithCost chain a.1).1,
        (compute D).work + chain.work + a.2 + (originalMaskWithCost chain a.1).2 + 10)) <$> t) =
      lower T (originalMask chain <$> p)
    rw [← map_lower, ← hplain]
    simp only [Functor.map_map, originalMaskWithCost_value]
  · rfl

private theorem core_budget_mono {u v : ℕ} (h : u ≤ v) (T : ℕ) :
    ChargedIntegerRounding.budget u T ≤ ChargedIntegerRounding.budget v T := by
  unfold ChargedIntegerRounding.budget RetainedBinarySampler.wordBudget
    EncodedRoundingRuntime.price RetainedChargedFairBits.workBound EncodedSampledRounding.epochCharge
    BinaryDrawTreeExecution.oneDrawBound EncodedRoundingState.candidateBound
    EncodedCandidateOutput.operationBound EncodedRoundingState.familyOverhead
    EncodedRoundingState.massBound EncodedRoundingState.sumOverhead
    EncodedRoundingState.roundOverhead EncodedRoundingState.eraseBound EncodedRoundingState.unionBound
    EncodedRoundingInput.cutBound EncodedIntegerShortestPaths.distanceBound
    EncodedRoundingInput.arrayBound EncodedTapeMaterialization.materializationBound
    EncodedTapeMaterialization.dictionaryBound
  dsimp only
  gcongr
  all_goals unfold EncodedRoundingInput.arrayBound; gcongr

private theorem prepared_budget_mono {u v : ℕ} (h : u ≤ v) (T : ℕ) :
    PreparedIntegerController.budget u T ≤ PreparedIntegerController.budget v T := by
  have hcore := core_budget_mono h T
  have hprep := ChargedRoundingPreparation.budget_mono h
  have hparam : EncodedEpochParameters.operationBound u ≤ EncodedEpochParameters.operationBound v := by
    unfold EncodedEpochParameters.operationBound
    gcongr
  unfold PreparedIntegerController.budget
  omega

def budget (n T : ℕ) : ℕ := 3000 * n ^ 2 + 1142 * n + 121 + PreparedIntegerController.budget (6 * n) T

theorem budget_mono {u v : ℕ} (h : u ≤ v) (T : ℕ) : budget u T ≤ budget v T := by
  unfold budget
  gcongr
  exact prepared_budget_mono (Nat.mul_le_mul_left 6 h) T

theorem bitTree_charge {n : ℕ} (T : ℕ) (D : Input n) {a : Flags n × ℕ}
    (ha : a ∈ (ideal (bitTree T D)).support) :
    a.2 ≤ budget n T := by
  unfold bitTree at ha
  dsimp only at ha
  split_ifs at ha with h
  · let chain := expand D
    let cutoff := (expand_cutoff_bounds D h).1
    let t := PreparedIntegerController.bitTree T chain.data.adjacency chain.cutoff cutoff
    let observe (a : Flags chain.size × ℕ) : Flags n × ℕ :=
      ((originalMaskWithCost chain a.1).1,
        (compute D).work + chain.work + a.2 + (originalMaskWithCost chain a.1).2 + 10)
    change a ∈ (ideal (map observe t)).support at ha
    rw [show ideal (map observe t) = (ideal t).map observe from law_map _ _ _] at ha
    obtain ⟨result, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    have hpos : 0 < (compute D).total.realValue := by
      rw [compute_total]
      exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp h)
    have hchain := computed_work_bound D hpos
    have hproj := computed_originalMask_work D hpos result.1
    have hcore := (PreparedIntegerController.bitTree_charge T _ _ _ hr).trans
      (prepared_budget_mono (expand_size_bound D hpos) T)
    change (compute D).work + chain.work + result.2 + (originalMaskWithCost chain result.1).2 + 10 ≤ _
    change chain.work ≤ _ at hchain
    change (originalMaskWithCost chain result.1).2 ≤ _ at hproj
    rw [compute_work]
    unfold budget
    omega
  · have he : a = (Vector.replicate n false, (compute D).work + 4 * n + 10) := by
      simpa [ideal, law] using ha
    rw [he]
    dsimp only
    rw [compute_work]
    unfold budget
    omega

end DirectedFlowCutGap.ChargedUniformRounding
