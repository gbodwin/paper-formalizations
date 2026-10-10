import LightEFTSpanners.ContractedCoreCuts
import LightEFTSpanners.MultigraphPartitionCounts

namespace LightEFTSpanners.MultigraphCuts
open Finset
variable {V I : Type*} [Fintype V] [Fintype I] [Nontrivial I]
attribute [local instance] Classical.propDecidable

/-- Contracting the outside preserves its boundary exactly as original edge
identities. Loops created inside the contracted complement do not enter it. -/
theorem collapse_outside_cut (G : SimpleGraph V) (K : Set V) :
    ((Graph.ofSimpleGraph G).map (collapseOutside K)).edgeCut {v | v=none}=
      (ConnectivityCuts.edges G K:Set (Sym2 V)) := by
  classical
  rw [edgeCut_map]
  have hp : collapseOutside K ⁻¹' {v | v=none}=Kᶜ := by
    ext v
    by_cases hv : v∈K <;> simp [collapseOutside,hv]
  rw [hp,edgeCut_compl,ofSimpleGraph_cut]

/-- Every genuine nontrivial partition of a minimal deficient core meets the
spanning-tree packing cut criterion in its actual complement contraction.
This discharges the counting part of CS09 Lemma 2.5. It deliberately does not
assume or conclude the as-yet-unproved Nash-Williams/Tutte existence theorem. -/
theorem minimal_core_partition_budget (G : SimpleGraph V) (K : Finset V) {k : ℕ}
    (hsmall : (ConnectivityCuts.edges G (K:Set V)).card≤2*k)
    (hmin : ∀ A : Finset V,A⊂K → A.Nonempty →
      2*k≤(ConnectivityCuts.edges G (A:Set V)).card)
    (assign : ↑(K:Set V) → I) (hsurj : Function.Surjective assign) :
    k*(Fintype.card I-1)≤
      (partitionCrossings ((Graph.ofSimpleGraph G).map (collapseOutside (K:Set V)))
        (Option.map assign)).card := by
  classical
  apply partition_crossing_budget
  · intro i
    obtain ⟨a,ha⟩ := hsurj i
    obtain ⟨j,hji⟩ := exists_ne i
    obtain ⟨b,hb⟩ := hsurj j
    exact minimal_core_contracted_cut_lower G K hmin a b
      {v | Option.map assign v=some i}
      (by change some (assign a)=some i; exact congrArg some ha)
      (by
        change some (assign b)≠some i
        intro heq
        exact hji (hb.symm.trans (Option.some.inj heq)))
  · have hp : {v : Option (K:Set V) | Option.map assign v=none}={v | v=none} := by
      ext v
      cases v <;> simp
    rw [hp,collapse_outside_cut]
    simpa using hsmall
end LightEFTSpanners.MultigraphCuts
