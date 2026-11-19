import DirectedFlowCutGap.ChargedUniformRounding
import DirectedFlowCutGap.EncodedWeightedRounding

/-!
# Word charges of the weighted mass rounder

The actual port preparation and unit-cost dispatch are retained once.
The expanded branch composes the uniform-chain controller and the
charged projection through the full clone fibers. The inherited word
model includes the integer preparation and binary sampler charges.
-/

namespace DirectedFlowCutGap.ChargedWeightedRounding

open BinaryArithmetic FiniteDrawTrees LazyFairBitTrees RetainedGridState
open EncodedUnitCostReplication EncodedUnitCostPreparation
open IntegralNetworkFlow.Tabulated

def bitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (Flags n × ℕ) :=
  let r := prepareAndReduce D
  match r.reduced with
  | .zero mask _ =>
    let out := r.prepared.pullbackMaskWithCost mask
    .pure (out.1, r.work + out.2 + 5)
  | .replicated _ counts replica _ =>
    map (fun (mask, paid) =>
      let out := r.prepared.pullbackSampleWithCost counts replica mask
      (out.1, r.work + paid + out.2 + 5))
      (ChargedUniformRounding.bitTree T replica.input)

theorem bitTree_value {n : ℕ} (T : ℕ) (D : Input n) :
    map Prod.fst (bitTree T D) = EncodedWeightedRounding.bitTree T D := by
  unfold bitTree EncodedWeightedRounding.bitTree EncodedWeightedRounding.tree
  dsimp only
  have hreduce : (prepareAndReduce D).reduced = (build D).data.reduce := rfl
  rw [hreduce]
  by_cases h : (build D).data.totals.objective.num = 0
  · rw [Input.reduce_zero _ h]
    rfl
  · rw [Input.reduce_positive _ h]
    let p := build D
    let replica := materialize p.data p.data.counts
    let cost := (prepareAndReduce D).work
    let t := ChargedUniformRounding.bitTree T replica.input
    let plain := EncodedUniformRounding.tree replica.input
    have ht : Prod.fst <$> t = lower T plain := ChargedUniformRounding.bitTree_value ..
    change Prod.fst <$> ((fun a =>
      ((p.pullbackSampleWithCost p.data.counts replica a.1).1,
        cost + a.2 + (p.pullbackSampleWithCost p.data.counts replica a.1).2 + 5)) <$> t) =
      lower T (p.pullbackSample p.data.counts replica <$> plain)
    rw [← ChargedUniformRounding.map_lower, ← ht]
    simp only [Functor.map_map, Prepared.pullbackSampleWithCost_value]

def budget (n T : ℕ) : ℕ :=
  9*n^2*(CountedSearch.searchBound (3*n) 24+224)+640*n^4+108*n^3+316*n^2+1011*n+206+
    ChargedUniformRounding.budget (4*n^2) T

theorem budget_mono {u v : ℕ} (h : u ≤ v) (T : ℕ) : budget u T ≤ budget v T := by
  unfold budget CountedSearch.searchBound CountedSearch.visitBound
  gcongr
  apply ChargedUniformRounding.budget_mono
  gcongr

theorem bitTree_charge {n : ℕ} (T : ℕ) (D : Input n) {out : Flags n × ℕ}
    (ho : out ∈ (ideal (bitTree T D)).support) : out.2 ≤ budget n T := by
  have hprep := prepareAndReduce_work D
  unfold bitTree at ho
  dsimp only at ho
  have hreduce : (prepareAndReduce D).reduced = (build D).data.reduce := rfl
  rw [hreduce] at ho
  by_cases h : (build D).data.totals.objective.num = 0
  · rw [Input.reduce_zero _ h] at ho
    let p := build D
    let q := p.pullbackMaskWithCost p.data.zeroMask
    change out ∈ (PMF.pure (q.1, (prepareAndReduce D).work + q.2 + 5)).support at ho
    have hv := (PMF.mem_support_pure_iff _ _).mp ho
    rw [hv]
    have hcost := pullback_work_bound D p.data.zeroMask
    change q.2 ≤ _ at hcost
    unfold budget
    dsimp only
    omega
  · rw [Input.reduce_positive _ h] at ho
    have hn : 0 < n := by
      by_contra hn
      obtain rfl : n = 0 := by omega
      exact h (empty_objective_zero D)
    let p := build D
    let replica := materialize p.data p.data.counts
    let t := ChargedUniformRounding.bitTree T replica.input
    let observe (a : Flags (cloneList p.data.counts).length × ℕ) : Flags n × ℕ :=
      let result := p.pullbackSampleWithCost p.data.counts replica a.1
      (result.1, (prepareAndReduce D).work + a.2 + result.2 + 5)
    change out ∈ (ideal (map observe t)).support at ho
    rw [show ideal (map observe t) = (ideal t).map observe from law_map _ _ _] at ho
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
    have hsize := build_clone_count D hn h
    have hcore := (ChargedUniformRounding.bitTree_charge T replica.input ha).trans
      (ChargedUniformRounding.budget_mono hsize T)
    have hcost := pullbackSample_work_bound D hn h a.1
    change (p.pullbackSampleWithCost p.data.counts replica a.1).2 ≤ _ at hcost
    change (prepareAndReduce D).work + a.2 + (p.pullbackSampleWithCost p.data.counts replica a.1).2 + 5 ≤ _
    unfold budget
    omega

end DirectedFlowCutGap.ChargedWeightedRounding
