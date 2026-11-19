import DirectedFlowCutGap.PhysicalIntegerRounding
import DirectedFlowCutGap.LiteralTapeComposition
import DirectedFlowCutGap.ChargedSizeRounding

/-! Feed the actual constructed chains into the physical integer controller. -/

namespace DirectedFlowCutGap.PhysicalVertexRounding

open BinaryArithmetic FiniteDrawTrees RetainedGridState
open EncodedUnitCostReplication
open LiteralTapeComposition (execute execute_map)

def project {n m : ℕ} (f : Flags m → Flags n × ℕ) (overhead : ℕ) (input : PhysicalIntegerRounding.Result m) : PhysicalIntegerRounding.Result n :=
  let out := f input.mask
  ⟨out.1,input.suffix,overhead+input.paid+out.2⟩

theorem project_observe {n m : ℕ} (f : Flags m → Flags n × ℕ) (g : Flags m → Flags n)
    (eq : ∀ a, (f a).1=g a) (charge : ℕ) (input : Option (PhysicalIntegerRounding.Result m)) :
    (input.map (project f charge)).map PhysicalIntegerRounding.Result.observe =
      (input.map PhysicalIntegerRounding.Result.observe).map (fun (a,tape) => (g a,tape)) := by
  cases input with
  | none => rfl
  | some x => simp [project,PhysicalIntegerRounding.Result.observe,eq]

section Uniform

open EncodedUniformWeightParameters EncodedUniformChain EncodedUniformOutput RawNonnegativeRational

def uniform {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Option (PhysicalIntegerRounding.Result n) :=
  let p := compute D
  if Code.one.le p.total = true then
    let chain := materialize p.ports p.average p.counts
    (PhysicalIntegerRounding.run T chain.data.adjacency chain.cutoff tape).map
      (project (originalMaskWithCost chain) (p.work+chain.work+10))
  else some ⟨Vector.replicate n false,tape,p.work+4*n+10⟩

theorem uniform_observe {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (uniform T D tape).map PhysicalIntegerRounding.Result.observe = execute T (EncodedUniformRounding.tree D) tape := by
  unfold uniform EncodedUniformRounding.tree
  dsimp only
  split_ifs with h
  · let chain := expand D
    change ((PhysicalIntegerRounding.run T chain.data.adjacency chain.cutoff tape).map
      (project (originalMaskWithCost chain) ((compute D).work+chain.work+10))).map PhysicalIntegerRounding.Result.observe =
      execute T (map (originalMask chain) (EncodedIntegerRounding.tree chain.data.adjacency chain.cutoff
        (expand_cutoff_bounds D h).1)) tape
    rw [project_observe _ _ (originalMaskWithCost_value chain),execute_map]
    rw [PhysicalIntegerRounding.run_observe T chain.data.adjacency chain.cutoff (expand_cutoff_bounds D h).1]
    rfl
  · rfl

end Uniform

section Weighted

open EncodedUnitCostPreparation

def weighted {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Option (PhysicalIntegerRounding.Result n) :=
  let r := prepareAndReduce D
  match r.reduced with
  | .zero mask _ =>
    let out := r.prepared.pullbackMaskWithCost mask
    some ⟨out.1,tape,r.work+out.2+5⟩
  | .replicated _ counts replica _ =>
    (uniform T replica.input tape).map
      (project (r.prepared.pullbackSampleWithCost counts replica) (r.work+5))

set_option maxHeartbeats 1400000 in
theorem weighted_observe {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (weighted T D tape).map PhysicalIntegerRounding.Result.observe = execute T (EncodedWeightedRounding.tree D) tape := by
  unfold weighted EncodedWeightedRounding.tree
  dsimp only
  have reduce : (prepareAndReduce D).reduced = (build D).data.reduce := rfl
  rw [reduce]
  by_cases h : (build D).data.totals.objective.num=0
  · rw [Input.reduce_zero _ h]
    simp only [LiteralTapeComposition.execute_pure,Option.map_some,PhysicalIntegerRounding.Result.observe,Prepared.pullbackMaskWithCost]
  · rw [Input.reduce_positive _ h]
    let p := build D
    let replica := materialize p.data p.data.counts
    change ((uniform T replica.input tape).map
      (project (p.pullbackSampleWithCost p.data.counts replica) ((prepareAndReduce D).work+5))).map PhysicalIntegerRounding.Result.observe =
      execute T (map (p.pullbackSample p.data.counts replica) (EncodedUniformRounding.tree replica.input)) tape
    rw [project_observe _ _ (Prepared.pullbackSampleWithCost_value p p.data.counts replica),uniform_observe,execute_map]

end Weighted

section Size

open EncodedHeavyVertexPreparation EncodedCubeRootThreshold

def size {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) : Option (PhysicalIntegerRounding.Result n) :=
  let prep := prepare D
  (weighted T prep.1.data tape).map (project (combinedMaskWithCost prep.1) (prep.2+5))

theorem size_observe {n : ℕ} (T : ℕ) (D : Input n) (tape : Bits) :
    (size T D tape).map PhysicalIntegerRounding.Result.observe = execute T (EncodedSizeRounding.tree D) tape := by
  rw [size,EncodedSizeRounding.tree,project_observe _ _ (combinedMaskWithCost_value _),weighted_observe,execute_map]

end Size
end DirectedFlowCutGap.PhysicalVertexRounding
