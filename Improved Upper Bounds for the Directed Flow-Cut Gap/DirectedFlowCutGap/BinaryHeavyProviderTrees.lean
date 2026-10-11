import DirectedFlowCutGap.BinaryHeavyPrefix
import DirectedFlowCutGap.HeavyCutProvider
import DirectedFlowCutGap.FiniteSupportTrees

/-! A branch-preserving, proof-indexed tree for the actual heavy provider.
It adds the erased cut-validity proof at the returned leaf. Query metadata and
the specified local ledger are unchanged, and no branch is filtered or retried.
Raw materialization, budget construction and physical runtime remain separate. -/
namespace DirectedFlowCutGap.BinaryHeavyProviderTrees
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteDrawTrees LazyFairBitTrees BinaryFractionalRows BinarySamplerMetadata
open HeavyCutProvider

private theorem query_ideal {n : ℕ} (D : EncodedUnitCostReplication.Input n)
    (extra : ℕ) (state : Ledger) :
    ideal (BinaryHeavyPrefix.tree D extra state)=(StatefulHeavyQuery.run D extra).run state := by
  have h := FiniteBinaryPrefix.output_law (BinaryHeavyPrefix.within D extra state)
    (BinaryHeavyPrefix.binary D extra state)
  rw [← BinaryHeavyPrefix.same_stream D extra state] at h
  exact h.symm.trans (BinaryHeavyPrefix.output_law D extra state)

def draw {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w : Row n)
    (extra : ℕ) (state : Ledger) : BinaryZeroAvoidingProvider.CutProvider FiniteDrawTrees.Tree
      (columns adjacency w) := fun c =>
  FiniteSupportTrees.mapSupport (BinaryHeavyPrefix.tree (input adjacency w c) extra state)
    (fun out ho => answer adjacency w c extra state out (by
      rwa [query_ideal] at ho))

theorem binary {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (extra : ℕ) (state : Ledger) : Binary (draw adjacency w extra state c) :=
  FiniteSupportTrees.binary (BinaryHeavyPrefix.binary (input adjacency w c) extra state) _

theorem within {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (extra : ℕ) (state : Ledger) :
    Within (BinaryHeavyPrefix.budget (input adjacency w c) extra)
      (draw adjacency w extra state c) :=
  FiniteSupportTrees.within (BinaryHeavyPrefix.within (input adjacency w c) extra state) _

private theorem support_transport {A B : Type} (μ ν : PMF A) (h : μ=ν)
    (f : ∀ a∈ν.support,PMF B) :
    μ.bindOnSupport (fun a ha => f a (h ▸ ha))=ν.bindOnSupport f := by
  cases h
  rfl

theorem ideal_eq {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (extra : ℕ) (state : Ledger) :
    ideal (draw adjacency w extra state c)=HeavyCutProvider.draw adjacency w extra state c := by
  unfold draw
  rw [FiniteSupportTrees.law]
  exact support_transport _ _ (query_ideal (input adjacency w c) extra state)
    (fun out ho => PMF.pure (answer adjacency w c extra state out ho))

/-- The same actual reader consumes this query's bits in the caller's stream. -/
def read {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (extra : ℕ) (state : Ledger) : StateM (List (Fin 2))
      (BinaryZeroAvoidingProvider.CutAnswer (columns adjacency w)) :=
  FiniteBinaryPrefix.run (draw adjacency w extra state c)

theorem output_law {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (extra : ℕ) (state : Ledger) :
    (FiniteBinaryPrefix.prefixLaw (BinaryHeavyPrefix.budget (input adjacency w c) extra)).map
      (fun xs => ((read adjacency w c extra state).run xs).1)=
      HeavyCutProvider.draw adjacency w extra state c := by
  rw [read,FiniteBinaryPrefix.output_law (within adjacency w c extra state)
    (binary adjacency w c extra state),ideal_eq]

theorem suffix {n : ℕ} (adjacency : RetainedGridState.PairFlags n) (w c : Row n)
    (extra : ℕ) (state : Ledger) (xs : List (Fin 2))
    (hlen : BinaryHeavyPrefix.budget (input adjacency w c) extra≤xs.length) :
    ∃ used≤BinaryHeavyPrefix.budget (input adjacency w c) extra,
      ((read adjacency w c extra state).run xs).2=xs.drop used :=
  FiniteBinaryPrefix.suffix (within adjacency w c extra state)
    (binary adjacency w c extra state) xs hlen

end
end DirectedFlowCutGap.BinaryHeavyProviderTrees
