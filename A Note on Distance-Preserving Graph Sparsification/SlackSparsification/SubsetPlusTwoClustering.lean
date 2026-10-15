import SlackSparsification.SubsetPlusTwoIncidence

/-! Exact integer clustering certificate required from CGK13 Lemma 5.
No existence of this certificate is assumed as an axiom or proved in this module. -/
namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Target of the still-open greedy clustering construction. -/
structure ClusteringCertificate (G : SimpleGraph V) (d : ℕ) where
  base : SimpleGraph V
  base_le : base ≤ G
  clusters : Finset (Finset V)
  pairwise_disjoint : ∀ C ∈ clusters, ∀ D ∈ clusters, C ≠ D → Disjoint C D
  cluster_card : ∀ C ∈ clusters, C.card = d
  diameter : ∀ C ∈ clusters, ClusterDiameterTwo base C
  intra : ∀ C ∈ clusters, ∀ a ∈ C, ∀ b ∈ C, G.Adj a b → base.Adj a b
  missing : ∀ a b, G.Adj a b → ¬ base.Adj a b →
    ∃ C ∈ clusters, ∃ D ∈ clusters, a ∈ C ∧ b ∈ D ∧ C ≠ D
  cluster_count : clusters.card * d ≤ Fintype.card V
  edge_budget : base.edgeFinset.card ≤ 2 * Fintype.card V * d

omit [Fintype V] [DecidableEq V] in
/-- A star in the retained graph gives the required diameter, including
centers outside the cluster. -/
theorem star_cluster_diameter (H : SimpleGraph V) (C : Finset V) (center : V)
    (hstar : ∀ v ∈ C, H.Adj v center) : ClusterDiameterTwo H C := by
  intro a ha b hb
  calc
    H.edist a b ≤ H.edist a center + H.edist center b := H.edist_triangle
    _ = 1 + 1 := by rw [edist_eq_one_iff_adj.mpr (hstar a ha),
      edist_eq_one_iff_adj.mpr (hstar b hb).symm]
    _ = 2 := by norm_num

omit [Fintype V] in
/-- Disjoint clusters give exact unique ownership, rather than only coverage. -/
theorem unique_owner_card (Cs : Finset (Finset V))
    (hdisj : ∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D)
    (v : V) (A : Finset V) (hA : A ∈ Cs) (hv : v ∈ A) :
    (Cs.filter fun C => v ∈ C).card = 1 := by
  have he : Cs.filter (fun C => v ∈ C) = {A} := by
    ext C
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hC, hvC⟩
      by_contra hne
      exact (Finset.disjoint_left.mp (hdisj C hC A hA hne)) hvC hv
    · rintro rfl
      exact ⟨hA, hv⟩
  rw [he, card_singleton]

/-- Lemma 6 from the explicit clustering certificate, for any collection of
missing indexed steps of an actual shortest walk. -/
theorem missing_count_of_certificate (G : SimpleGraph V) (d : ℕ)
    (cert : ClusteringCertificate G d) {s t : V} (p : G.Walk s t)
    (hp : p.length = G.dist s t) (M : Finset ℕ)
    (hM : ∀ i ∈ M, i < p.length ∧ ¬ cert.base.Adj (p.getVert i) (p.getVert (i + 1))) :
    M.card ≤ 2 * (cert.clusters.filter fun C => (clusterPositions p C).Nonempty).card := by
  let Cs := cert.clusters.filter fun C => (clusterPositions p C).Nonempty
  have hdisj : ∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D := by
    intro C hC D hD hne
    exact cert.pairwise_disjoint C (mem_filter.mp hC).1 D (mem_filter.mp hD).1 hne
  apply missing_count_le_twice_clusters G cert.base p hp Cs
  · intro C hC
    exact diameter_mono cert.base_le C (cert.diameter C (mem_filter.mp hC).1)
  · intro C hC
    exact cert.intra C (mem_filter.mp hC).1
  · exact hM
  · intro i hi
    obtain ⟨C, hC, D, hD, hiC, _⟩ :=
      cert.missing _ _ (p.adj_getVert_succ (hM i hi).1) (hM i hi).2
    apply unique_owner_card Cs hdisj _ C ?_ hiC
    exact mem_filter.mpr ⟨hC, ⟨i, (mem_clusterPositions p C i).mpr ⟨(hM i hi).1.le, hiC⟩⟩⟩
  · intro i hi
    obtain ⟨C, hC, D, hD, _, hiD, _⟩ :=
      cert.missing _ _ (p.adj_getVert_succ (hM i hi).1) (hM i hi).2
    apply unique_owner_card Cs hdisj _ D ?_ hiD
    exact mem_filter.mpr ⟨hD, ⟨i + 1, (mem_clusterPositions p D (i + 1)).mpr
      ⟨by have := (hM i hi).1; omega, hiD⟩⟩⟩

end SlackSparsification.SubsetPlusTwo
