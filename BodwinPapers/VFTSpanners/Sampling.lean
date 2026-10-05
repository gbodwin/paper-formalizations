import BodwinPapers.VFTSpanners.BlockingSet
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Exact fixed-size sampling for the blocking-set argument

Double counting over all `r`-vertex subsets gives the two survival probabilities
in Lemma 4 without asymptotic notation or a probability-space convention.
-/

namespace BodwinPapers.VFTSpanners

open Finset
open scoped BigOperators

variable {V I : Type*} [DecidableEq V]

/-- Items whose entire support lies in a sampled vertex set. -/
def included (items : Finset I) (sites : I → Finset V) (S : Finset V) : Finset I :=
  items.filter (fun i => sites i ⊆ S)

/-- Count each supported item over all fixed-size samples. -/
theorem sum_included_card (U : Finset V) (items : Finset I)
    (sites : I → Finset V) (r d : ℕ) (hdr : d ≤ r)
    (hsites : ∀ i ∈ items, sites i ⊆ U ∧ (sites i).card = d) :
    ∑ S ∈ U.powersetCard r, (included items sites S).card =
      items.card * Nat.choose (U.card - d) (r - d) := by
  classical
  calc
    _ = ∑ S ∈ U.powersetCard r, ∑ i ∈ items, if sites i ⊆ S then 1 else 0 := by
      simp only [included, card_eq_sum_ones, sum_filter]
    _ = ∑ i ∈ items, ∑ S ∈ U.powersetCard r, if sites i ⊆ S then 1 else 0 :=
      sum_comm
    _ = ∑ i ∈ items, ((U.powersetCard r).filter (sites i ⊆ ·)).card := by
      simp only [card_eq_sum_ones, sum_filter]
    _ = ∑ _ ∈ items, Nat.choose (U.card - d) (r - d) := by
      apply sum_congr rfl
      intro i hi
      obtain ⟨hsub, hcard⟩ := hsites i hi
      rw [card_filter_powersetCard_subset (sites i) U r hsub (hcard ▸ hdr), hcard]
    _ = _ := by simp

/-- A blocker survives exactly when its three distinct vertices survive. -/
def blockerSites (b : V × Sym2 V) : Finset V := insert b.1 b.2.toFinset

/-- Original edge labels retained after sampling and deleting blocked edges. -/
def retainedEdges (E : Finset (Sym2 V)) (B : Finset (V × Sym2 V))
    (S : Finset V) : Finset (Sym2 V) :=
  included E Sym2.toFinset S \ (included B blockerSites S).image Prod.snd

/-- One blocked edge costs at most one surviving blocking pair. -/
theorem sampled_edge_count_le (E : Finset (Sym2 V)) (B : Finset (V × Sym2 V))
    (S : Finset V) :
    (included E Sym2.toFinset S).card ≤
      (retainedEdges E B S).card + (included B blockerSites S).card := by
  classical
  let A := included E Sym2.toFinset S
  let D := (included B blockerSites S).image Prod.snd
  have h := card_sdiff_add_card_inter A D
  have hi : (A ∩ D).card ≤ (included B blockerSites S).card :=
    (card_le_card inter_subset_right).trans (card_image_le)
  change A.card ≤ (A \ D).card + _
  omega

/-- The exact edge survival count: each edge has two distinct endpoints. -/
theorem sum_sampled_edges (U : Finset V) (E : Finset (Sym2 V)) (r : ℕ)
    (hr : 2 ≤ r) (hE : ∀ e ∈ E, e.toFinset ⊆ U ∧ ¬ e.IsDiag) :
    ∑ S ∈ U.powersetCard r, (included E Sym2.toFinset S).card =
      E.card * Nat.choose (U.card - 2) (r - 2) := by
  apply sum_included_card U E Sym2.toFinset r 2 hr
  intro e he
  exact ⟨(hE e he).1, Sym2.card_toFinset_of_not_isDiag e (hE e he).2⟩

/-- The exact blocker survival count: its vertex is not either endpoint. -/
theorem sum_sampled_blockers (U : Finset V) (E : Finset (Sym2 V))
    (B : Finset (V × Sym2 V)) (r : ℕ) (hr : 3 ≤ r)
    (hE : ∀ e ∈ E, e.toFinset ⊆ U ∧ ¬ e.IsDiag)
    (hB : ∀ b ∈ B, b.2 ∈ E ∧ b.1 ∈ U ∧ b.1 ∉ b.2) :
    ∑ S ∈ U.powersetCard r, (included B blockerSites S).card =
      B.card * Nat.choose (U.card - 3) (r - 3) := by
  apply sum_included_card U B blockerSites r 3 hr
  intro b hb
  obtain ⟨hbe, hbU, hnot⟩ := hB b hb
  obtain ⟨hesub, hecard⟩ := hE b.2 hbe
  have hnot' : b.1 ∉ b.2.toFinset := by simpa using hnot
  constructor
  · apply insert_subset
    · exact hbU
    · exact hesub
  · simp [blockerSites, card_insert_of_notMem hnot',
      Sym2.card_toFinset_of_not_isDiag b.2 hecard]

/-- Exact, division-free form of the expectation inequality in Lemma 4. -/
theorem sum_retained_edges_bound (U : Finset V) (E : Finset (Sym2 V))
    (B : Finset (V × Sym2 V)) (r : ℕ) (hr : 3 ≤ r)
    (hE : ∀ e ∈ E, e.toFinset ⊆ U ∧ ¬ e.IsDiag)
    (hB : ∀ b ∈ B, b.2 ∈ E ∧ b.1 ∈ U ∧ b.1 ∉ b.2) :
    E.card * Nat.choose (U.card - 2) (r - 2) ≤
      (∑ S ∈ U.powersetCard r, (retainedEdges E B S).card) +
        B.card * Nat.choose (U.card - 3) (r - 3) := by
  have h := sum_le_sum (fun S (_ : S ∈ U.powersetCard r) =>
    sampled_edge_count_le E B S)
  rw [sum_add_distrib, sum_sampled_edges U E r (by omega) hE,
    sum_sampled_blockers U E B r hr hE hB] at h
  exact h

/-- A fixed-size sample meets or exceeds the average surviving edge count.
Together with `prunedGraph_no_short_cycle`, this is the existential step
in Lemma 4, with exact finite-size coefficients. -/
theorem exists_dense_sample (U : Finset V) (E : Finset (Sym2 V))
    (B : Finset (V × Sym2 V)) (r : ℕ) (hr : 3 ≤ r) (hrn : r ≤ U.card)
    (hE : ∀ e ∈ E, e.toFinset ⊆ U ∧ ¬ e.IsDiag)
    (hB : ∀ b ∈ B, b.2 ∈ E ∧ b.1 ∈ U ∧ b.1 ∉ b.2) :
    ∃ S ∈ U.powersetCard r,
      E.card * Nat.choose (U.card - 2) (r - 2) ≤
        Nat.choose U.card r * (retainedEdges E B S).card +
          B.card * Nat.choose (U.card - 3) (r - 3) := by
  obtain ⟨S, hS, hmax⟩ := exists_max_image (U.powersetCard r)
    (fun S => (retainedEdges E B S).card) (powersetCard_nonempty.mpr hrn)
  refine ⟨S, hS, (sum_retained_edges_bound U E B r hr hE hB).trans ?_⟩
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _ ∈ U.powersetCard r, (retainedEdges E B S).card :=
      sum_le_sum hmax
    _ = _ := by simp

/-- Retained edge labels are exactly the adjacencies used by `prunedGraph`. -/
theorem mem_retainedEdges (E : Finset (Sym2 V)) (B : Finset (V × Sym2 V))
    (S : Finset V) (e : Sym2 V) :
    e ∈ retainedEdges E B S ↔
      e ∈ E ∧ e.toFinset ⊆ S ∧ ∀ v ∈ S, (v, e) ∉ B := by
  classical
  constructor
  · intro h
    obtain ⟨he, hd⟩ := mem_sdiff.mp h
    obtain ⟨heE, heS⟩ := mem_filter.mp he
    refine ⟨heE, heS, ?_⟩
    intro v hv hvB
    apply hd
    apply mem_image.mpr
    refine ⟨(v, e), ?_, rfl⟩
    exact mem_filter.mpr ⟨hvB, insert_subset hv heS⟩
  · rintro ⟨heE, heS, havoid⟩
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨heE, heS⟩, ?_⟩
    intro h
    obtain ⟨b, hb, hbe⟩ := mem_image.mp h
    obtain ⟨hbB, hbS⟩ := mem_filter.mp hb
    have hvS : b.1 ∈ S := hbS (mem_insert_self _ _)
    exact havoid b.1 hvS (hbe ▸ hbB)

section GraphCounts

variable [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Relabeling pruned edges by their original endpoints gives precisely the
retained edge set used in the counting argument. -/
theorem image_pruned_edgeFinset (G : SimpleGraph V) (B : Finset (V × Sym2 V))
    (S : Finset V) :
    (prunedGraph G (S : Set V) (B : Set (V × Sym2 V))).edgeFinset.image
        (Sym2.map (Subtype.val : {x : V // x ∈ S} → V)) =
      retainedEdges G.edgeFinset B S := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    revert he'
    refine Sym2.ind (fun x y hxy => ?_) e'
    have hadj : (prunedGraph G (S : Set V) (B : Set (V × Sym2 V))).Adj x y :=
      by simpa using hxy
    apply (mem_retainedEdges _ _ _ _).mpr
    refine ⟨by simpa using hadj.1, ?_, ?_⟩
    · change s(x.val, y.val).toFinset ⊆ S
      rw [Sym2.toFinset_mk_eq]
      simpa only [insert_subset_iff, singleton_subset_iff] using
        And.intro x.property y.property
    · simpa using hadj.2
  · intro he
    revert he
    refine Sym2.ind (fun x y hxy => ?_) e
    obtain ⟨heE, heS, havoid⟩ := (mem_retainedEdges _ _ _ _).mp hxy
    have hx : x ∈ S := heS (by simp [Sym2.toFinset_mk_eq])
    have hy : y ∈ S := heS (by simp [Sym2.toFinset_mk_eq])
    apply mem_image.mpr
    refine ⟨s((⟨x, hx⟩ : {x : V // x ∈ S}), (⟨y, hy⟩ : {x : V // x ∈ S})), ?_, rfl⟩
    apply SimpleGraph.mem_edgeFinset.mpr
    apply (SimpleGraph.mem_edgeSet _).mpr
    exact ⟨by simpa using heE, by simpa using havoid⟩

/-- The counted original labels have exactly the pruned graph's edge count. -/
theorem card_pruned_edgeFinset (G : SimpleGraph V) (B : Finset (V × Sym2 V))
    (S : Finset V) :
    (prunedGraph G (S : Set V) (B : Set (V × Sym2 V))).edgeFinset.card =
      (retainedEdges G.edgeFinset B S).card := by
  rw [← image_pruned_edgeFinset G B S,
    card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

/-- Quantitative existence statement of Lemma 4 with exact binomial
coefficients and the cycle-elimination conclusion for the same graph. -/
theorem exists_dense_high_girth_sample (G : SimpleGraph V) (B : Finset (V × Sym2 V))
    (k r : ℕ) (hr : 3 ≤ r) (hrn : r ≤ Fintype.card V)
    (hB : IsBlockingSet G k (B : Set (V × Sym2 V))) :
    ∃ S : Finset V, S.card = r ∧
      G.edgeFinset.card * Nat.choose (Fintype.card V - 2) (r - 2) ≤
        Nat.choose (Fintype.card V) r *
          (prunedGraph G (S : Set V) (B : Set (V × Sym2 V))).edgeFinset.card +
            B.card * Nat.choose (Fintype.card V - 3) (r - 3) ∧
      ∀ a : (S : Set V), ∀ p : (prunedGraph G (S : Set V)
          (B : Set (V × Sym2 V))).Walk a a, p.IsCycle → k < p.length := by
  obtain ⟨S, hS, hcount⟩ := exists_dense_sample (univ : Finset V) G.edgeFinset B r hr
    (by simpa using hrn)
    (by intro e he; exact ⟨subset_univ _, G.not_isDiag_of_mem_edgeFinset he⟩)
    (by
      intro b hb
      have h := hB.1 hb
      exact ⟨SimpleGraph.mem_edgeFinset.mpr h.1, mem_univ _, h.2⟩)
  refine ⟨S, (mem_powersetCard.mp hS).2, ?_, ?_⟩
  · simpa only [card_univ, card_pruned_edgeFinset] using hcount
  · intro a p hp
    exact prunedGraph_cycle_length_gt hB (S : Set V) p hp

end GraphCounts

end BodwinPapers.VFTSpanners
