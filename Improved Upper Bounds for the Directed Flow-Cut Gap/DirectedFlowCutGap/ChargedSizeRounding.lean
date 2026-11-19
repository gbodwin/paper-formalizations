import DirectedFlowCutGap.ChargedWeightedRounding
import DirectedFlowCutGap.EncodedSizeRounding

/-!
# Word charges of the size-sensitive vertex rounder

The heavy-vertex extraction and final union carry their actual preparation
and projection charges. The weighted charged dispatcher receives the
retained survivor graph. Erasing charges recovers the same bit tree.
-/

namespace DirectedFlowCutGap.ChargedSizeRounding

open FiniteDrawTrees LazyFairBitTrees RetainedGridState
open EncodedUnitCostReplication EncodedHeavyVertexPreparation EncodedCubeRootThreshold

def bitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (Flags n × ℕ) :=
  let prep := prepare D
  map (fun (mask, paid) =>
    let combined := combinedMaskWithCost prep.1 mask
    (combined.1, prep.2 + paid + combined.2 + 5))
    (ChargedWeightedRounding.bitTree T prep.1.data)

theorem bitTree_value {n : ℕ} (T : ℕ) (D : Input n) :
    map Prod.fst (bitTree T D) = EncodedSizeRounding.bitTree T D := by
  let prep := prepare D
  let t := ChargedWeightedRounding.bitTree T prep.1.data
  let plain := EncodedWeightedRounding.tree prep.1.data
  have h : Prod.fst <$> t = lower T plain := ChargedWeightedRounding.bitTree_value ..
  change Prod.fst <$> ((fun a =>
    ((combinedMaskWithCost prep.1 a.1).1,
      prep.2 + a.2 + (combinedMaskWithCost prep.1 a.1).2 + 5)) <$> t) =
    lower T (combinedMask prep.1 <$> plain)
  rw [← ChargedUniformRounding.map_lower, ← h]
  simp only [Functor.map_map, combinedMaskWithCost_value]

def budget (n T : ℕ) : ℕ := 60*n^2+188*n+97+ChargedWeightedRounding.budget n T

theorem bitTree_charge {n : ℕ} (T : ℕ) (D : Input n) {out : Flags n × ℕ}
    (ho : out ∈ (ideal (bitTree T D)).support) : out.2 ≤ budget n T := by
  have hp := prepare_work D
  let prep := prepare D
  let t := ChargedWeightedRounding.bitTree T prep.1.data
  let observe (a : Flags prep.1.size × ℕ) : Flags n × ℕ :=
    let c := combinedMaskWithCost prep.1 a.1
    (c.1, prep.2 + a.2 + c.2 + 5)
  change out ∈ (ideal (map observe t)).support at ho
  rw [show ideal (map observe t) = (ideal t).map observe from law_map _ _ _] at ho
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  have hproj := build_combinedMask_work D (threshold n) a.1
  change (combinedMaskWithCost prep.1 a.1).2 ≤ _ at hproj
  have hsize : prep.1.size ≤ n := build_size_le D (threshold n)
  have hc := (ChargedWeightedRounding.bitTree_charge T _ ha).trans (ChargedWeightedRounding.budget_mono hsize T)
  change prep.2 + a.2 + (combinedMaskWithCost prep.1 a.1).2 + 5 ≤ _
  change prep.2 ≤ _ at hp
  unfold budget
  omega

end DirectedFlowCutGap.ChargedSizeRounding
