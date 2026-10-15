import SlackSparsification.SubsetPlusTwoPurchase
import SlackSparsification.SubsetPlusTwoParameters

namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- A finite fold over every ordered demand. The sequence remains constant after
its last demand. Charges are actual source/cluster labels; edge increments
are telescoped, while satisfied demands persist by graph monotonicity. -/
theorem finite_purchase_fold (G : SimpleGraph V) (d : ℕ)
    (cert : ClusteringCertificate G d) (S : Finset V) :
    ∃ H : SimpleGraph V, cert.base ≤ H ∧ H ≤ G ∧
      H.edgeFinset.card ≤ cert.base.edgeFinset.card + 6 * (S.card * cert.clusters.card) ∧
      ∀ s ∈ S, ∀ t ∈ S, H.edist s t ≤ G.edist s t + 2 := by
  let L := (S ×ˢ S).toList
  let labels := S ×ˢ cert.clusters
  let State := {H : SimpleGraph V // cert.base ≤ H ∧ H ≤ G}
  have hex (i : ℕ) (X : State) : ∃ Y : State, ∃ Q : Finset (V × Finset V),
      X.val ≤ Y.val ∧ Q ⊆ labels ∧
      Y.val.edgeFinset.card ≤ X.val.edgeFinset.card + 2 * Q.card ∧
      (∀ st, L[i]? = some st → Y.val.edist st.1 st.2 ≤ G.edist st.1 st.2 + 2) ∧
      ∀ q ∈ Q, clusterEDist Y.val q.1 q.2 < clusterEDist X.val q.1 q.2 ∧
        clusterEDist Y.val q.1 q.2 ≤ clusterEDist G q.1 q.2 + 2 := by
    cases he : L[i]? with
    | none =>
      exact ⟨X, ∅, le_rfl, empty_subset _, by simp, by simp [he], by simp⟩
    | some st =>
      have hmem : st ∈ S ×ˢ S := by
        exact mem_toList.mp (List.mem_of_getElem? he)
      obtain ⟨K, Q, hXK, hKG, hQ, hc, hs, hcharge⟩ :=
        purchase_step G d cert S X.val X.property.1 X.property.2 st.1
          (mem_product.mp hmem).1 st.2 (mem_product.mp hmem).2
      refine ⟨⟨K, X.property.1.trans hXK, hKG⟩, Q, hXK, hQ, hc, ?_, hcharge⟩
      intro st' hst'
      have hst : st = st' := Option.some.inj (he.symm.trans hst')
      simpa [← hst] using hs
  choose next charge hstep hlabel hcost hsatisfy himprove using hex
  let initial : State := ⟨cert.base, le_rfl, cert.base_le⟩
  let states : ℕ → State := fun n => Nat.rec initial (fun i X => next i X) n
  let H : ℕ → SimpleGraph V := fun n => (states n).val
  let Q : ℕ → Finset (V × Finset V) := fun i => charge i (states i)
  have hsucc (i : ℕ) : H i ≤ H (i + 1) := hstep i (states i)
  have hmono : Monotone H := monotone_nat_of_le_succ hsucc
  have hsub (i : ℕ) : H i ≤ G := (states i).property.2
  have hQ (i : ℕ) : Q i ⊆ labels := hlabel i (states i)
  have hafter (i : ℕ) (q : V × Finset V) (hq : q ∈ Q i) :
      clusterEDist (H (i + 1)) q.1 q.2 < clusterEDist (H i) q.1 q.2 ∧
      clusterEDist (H (i + 1)) q.1 q.2 ≤ clusterEDist G q.1 q.2 + 2 :=
    himprove i (states i) q hq
  have hsum : (∑ i ∈ range L.length, 2 * (Q i).card) ≤ 6 * labels.card := by
    apply total_purchase_cost_le_six (range L.length) labels (fun i q => q ∈ Q i)
    · intro i _
      have heq : labels.filter (fun q => q ∈ Q i) = Q i := by
        ext q
        simp only [mem_filter]
        exact ⟨And.right, fun h => ⟨hQ i h, h⟩⟩
      rw [heq]
    · intro q _
      apply cluster_improvements_card_le_three G H hmono hsub q.1 q.2
      · intro i hi
        exact (hafter i q (mem_filter.mp hi).2).1
      · intro i hi
        exact (hafter i q (mem_filter.mp hi).2).2
  have htelescope (n : ℕ) :
      (H n).edgeFinset.card ≤ cert.base.edgeFinset.card + ∑ i ∈ range n, 2 * (Q i).card := by
    induction n with
    | zero => simp [H, states, initial]
    | succ n ih =>
      have hc : (H (n + 1)).edgeFinset.card ≤ (H n).edgeFinset.card + 2 * (Q n).card :=
        hcost n (states n)
      rw [sum_range_succ]
      omega
  refine ⟨H L.length, (states L.length).property.1, hsub _, ?_, ?_⟩
  · have hc := htelescope L.length
    have hl : labels.card = S.card * cert.clusters.card := card_product _ _
    rw [hl] at hsum
    omega
  · intro s hs t ht
    have hm : (s, t) ∈ L := mem_toList.mpr (mem_product.mpr ⟨hs, ht⟩)
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    have hget : L[i]? = some (s, t) := by rw [List.getElem?_eq_getElem hi, he]
    have hsat : (H (i + 1)).edist s t ≤ G.edist s t + 2 :=
      hsatisfy i (states i) (s, t) hget
    exact (edist_anti (hmono (by omega : i + 1 ≤ L.length))).trans hsat

/-- The concrete integer subset +2 construction, with no unproved construction premise. -/
theorem integer_subset_construction (G : SimpleGraph V) : IntegerSubsetConstruction G := by
  intro S d hd hsd
  obtain ⟨cert⟩ := clusteringCertificate_exists G d hd
  obtain ⟨H, _, hHG, hc, hsat⟩ := finite_purchase_fold G d cert S
  refine ⟨H, hHG, ?_, hsat⟩
  calc
    _ ≤ cert.base.edgeFinset.card + 6 * (S.card * cert.clusters.card) := hc
    _ ≤ 2 * Fintype.card V * d + 6 * S.card * cert.clusters.card := by
      have := cert.edge_budget
      nlinarith
    _ ≤ 8 * Fintype.card V * d := integer_subset_budget _ _ _ _ cert.cluster_count hsd

/-- Uniform subset +2 with the conservative explicit constant 16. -/
theorem uniform_subset_plus_two (G : SimpleGraph V) : UniformSubsetPlusTwo G 16 :=
  uniform_of_integer_subset_construction G (integer_subset_construction G)

end SlackSparsification.SubsetPlusTwo
