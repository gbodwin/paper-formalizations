import LengthExpander.DeletionCount
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000

namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

/-- Exact incidence double counting for fixed-size edge samples. This is the
finite uniform-sampling identity, with no independence approximation. -/
theorem fixed_size_incidence {I E : Type*} (F : Finset I) (E₀ : Finset E)
    (edges : I → Finset E) {r k : ℕ} (hrk : r ≤ k)
    (hsub : ∀ i ∈ F, edges i ⊆ E₀) (hsize : ∀ i ∈ F, (edges i).card = r) :
    (∑ S ∈ E₀.powersetCard k, (F.filter (fun i => edges i ⊆ S)).card) =
      F.card * (E₀.card-r).choose (k-r) := by
  classical
  calc
    _ = ∑ S ∈ E₀.powersetCard k, ∑ i ∈ F, if edges i ⊆ S then 1 else 0 := by
      simp only [card_eq_sum_ones, sum_filter]
    _ = ∑ i ∈ F, ∑ S ∈ E₀.powersetCard k, if edges i ⊆ S then 1 else 0 := sum_comm
    _ = ∑ i ∈ F, ((E₀.powersetCard k).filter (fun S => edges i ⊆ S)).card := by
      simp only [card_eq_sum_ones, sum_filter]
    _ = ∑ _i ∈ F, (E₀.card-r).choose (k-r) := by
      apply sum_congr rfl
      intro i hi
      rw [card_filter_powersetCard_subset (edges i) E₀ k (hsub i hi) (by rw [hsize i hi]; exact hrk), hsize i hi]
    _ = _ := by simp

/-- The exact survival identity expressed with falling factorials. -/
theorem choose_survival_identity {m k r : ℕ} (hrk : r ≤ k) :
    (m-r).choose (k-r) * m.descFactorial r = m.choose k * k.descFactorial r := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have h := Nat.choose_mul (n := m) hrk
  calc
    _ = r.factorial * (m.choose r * (m-r).choose (k-r)) := by ring
    _ = r.factorial * (m.choose k * k.choose r) := by rw [h]
    _ = _ := by ring

/-- A convenient polynomial survival bound. It differs from (k/m)^r by
only the harmless replacement of m with m+1-r, and is fully integral. -/
theorem choose_survival_bound {m k r : ℕ} (hrk : r ≤ k) :
    (m-r).choose (k-r) * (m+1-r)^r ≤ m.choose k * k^r := by
  calc
    _ ≤ (m-r).choose (k-r) * m.descFactorial r :=
      Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial m r)
    _ = m.choose k * k.descFactorial r := choose_survival_identity hrk
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow k r)

variable {V : Type*} {G : SimpleGraph V}

/-- A strictly increasing walk has no repeated edge, even before using
parallel-greedy distance exclusion. -/
theorem increasing_edges_nodup {index : Sym2 V → ℕ} {u v : V}
    {p : G.Walk u v} (hp : Increasing index p) : p.edges.Nodup := by
  have h : (p.edges.map index).Nodup := hp.imp (fun h => Nat.ne_of_lt h)
  exact List.Nodup.of_map index h

variable [Fintype V]

noncomputable def survivingCount (index : Sym2 V → ℕ) (r : ℕ)
    (S : Finset (Sym2 V)) : ℕ := by
  classical
  exact ((allMonotoneWalks G index r).filter (fun w => w.2.2.edges.toFinset ⊆ S)).card

/-- Exact average numerator for the actual finite family of increasing walks. -/
theorem sum_survivingCount (index : Sym2 V → ℕ) {r k : ℕ} (hrk : r ≤ k) :
    (∑ S ∈ G.edgeFinset.powersetCard k, survivingCount (G := G) index r S) =
      monotoneCount G index r * (G.edgeFinset.card-r).choose (k-r) := by
  classical
  have hsub : ∀ w ∈ allMonotoneWalks G index r, w.2.2.edges.toFinset ⊆ G.edgeFinset := by
    intro w hw e he
    exact G.mem_edgeFinset.mpr (w.2.2.edges_subset_edgeSet (by simpa using he))
  have hsize : ∀ w ∈ allMonotoneWalks G index r, w.2.2.edges.toFinset.card = r := by
    intro w hw
    obtain ⟨hl,hi⟩ := mem_allMonotoneWalks.mp hw
    rw [List.toFinset_card_of_nodup (increasing_edges_nodup hi), Walk.length_edges, hl]
  have heq := fixed_size_incidence (allMonotoneWalks G index r) G.edgeFinset
    (fun w => w.2.2.edges.toFinset) hrk hsub hsize
  rw [card_allMonotoneWalks] at heq
  convert heq using 1
  unfold survivingCount
  apply sum_congr rfl
  intro S hS
  congr 1
  ext w
  simp only [mem_filter,Finset.subset_iff,List.mem_toFinset]

/-- Walks surviving in a subgraph are exactly its walks, by explicit transfer. -/
theorem monotoneWalks_subgraph_card (index : Sym2 V → ℕ) (r : ℕ)
    {G' : SimpleGraph V} (hG : G' ≤ G) (u v : V) :
    (monotoneWalks G' index r u v).card =
      ((monotoneWalks G index r u v).filter
        (fun p => ∀ e ∈ p.edges, e ∈ G'.edgeSet)).card := by
  classical
  apply card_bij (fun p _ => p.mapLe hG)
  · intro p hp
    obtain ⟨hl,hi⟩ := mem_monotoneWalks.mp hp
    refine mem_filter.mpr ⟨mem_monotoneWalks.mpr ⟨?_,?_⟩,?_⟩
    · simpa only [Walk.length_mapLe] using hl
    · simpa only [Increasing,Walk.edges_mapLe_eq_edges] using hi
    · simpa only [Walk.edges_mapLe_eq_edges] using p.edges_subset_edgeSet
  · intro p hp q hq he
    exact Walk.map_injective_of_injective (f := SimpleGraph.Hom.ofLE hG)
      (fun _ _ h => h) u v he
  · intro p hp
    obtain ⟨hp,hs⟩ := mem_filter.mp hp
    obtain ⟨hl,hi⟩ := mem_monotoneWalks.mp hp
    refine ⟨p.transfer G' hs,mem_monotoneWalks.mpr ⟨?_,?_⟩,?_⟩
    · simpa only [Walk.length_transfer] using hl
    · simpa only [Increasing,Walk.edges_transfer] using hi
    · apply Walk.ext_support
      simp only [Walk.support_mapLe_eq_support,Walk.support_transfer]

/-- Retaining a subset of the graph's edge set creates precisely that many edges. -/
theorem retained_edgeSet {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset) :
    (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet = (S : Set (Sym2 V)) := by
  classical
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  exact ⟨fun h => h.1, fun he => ⟨he,G.not_isDiag_of_mem_edgeFinset (hS he)⟩⟩

/-- The concrete graph retained by an edge sample has exactly the enumerated
surviving monotone walks. -/
theorem survivingCount_eq_subgraph (index : Sym2 V → ℕ) (r : ℕ)
    {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset) :
    survivingCount (G := G) index r S =
      monotoneCount (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))) index r := by
  classical
  have hG : SimpleGraph.fromEdgeSet (S : Set (Sym2 V)) ≤ G := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet, retained_edgeSet hS]
    exact fun e he => G.mem_edgeFinset.mp (hS he)
  unfold survivingCount allMonotoneWalks monotoneCount
  simp only [filter_sigma,card_sigma]
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  rw [monotoneWalks_subgraph_card index r hG u v]
  congr 1
  ext p
  simp only [mem_filter,retained_edgeSet hS,Finset.mem_coe,Finset.subset_iff,List.mem_toFinset]

/-- Every fixed-size sample at the medium-counting threshold has many surviving walks. -/
theorem sample_medium_lower [Nonempty V] {index : Sym2 V → ℕ}
    (H : MatchingLabels G index) {r : ℕ} (hr : 0 < r)
    {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset)
    (hsize : Fintype.card V * r ≤ S.card) :
    Fintype.card V * r < 2 * survivingCount (G := G) index r S := by
  classical
  let G' := SimpleGraph.fromEdgeSet (S : Set (Sym2 V))
  have hG : G' ≤ G := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet]
    intro e he
    apply G.mem_edgeFinset.mp
    apply hS
    have he' : e ∈ (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).edgeSet := he
    rwa [retained_edgeSet hS] at he'
  have hmatching : MatchingLabels G' index := fun u v z hu hv hi =>
    H u v z (hG hu) (hG hv) hi
  have hfin : G'.edgeFinset = S := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset,G',retained_edgeSet hS,Finset.mem_coe]
  have hm : Fintype.card V * r ≤ G'.edgeFinset.card := by rw [hfin]; exact hsize
  rw [survivingCount_eq_subgraph index r hS]
  apply medium_counting hmatching hr
  convert hm using 1
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]

/-- Full counting before division: sum the deterministic medium lower bound
over all k=nr edge samples, then use the exact incidence identity. -/
theorem full_counting_binomial [Nonempty V] {index : Sym2 V → ℕ}
    (H : MatchingLabels G index) {r : ℕ} (hr : 0 < r)
    (hm : Fintype.card V * r ≤ G.edgeFinset.card) :
    (Fintype.card V * r) * G.edgeFinset.card.choose (Fintype.card V*r) <
      2 * monotoneCount G index r *
        (G.edgeFinset.card-r).choose (Fintype.card V*r-r) := by
  classical
  have hrk : r ≤ Fintype.card V*r := Nat.le_mul_of_pos_left r Fintype.card_pos
  have hsum := sum_lt_sum_of_nonempty (powersetCard_nonempty.mpr hm)
    (fun S hS => sample_medium_lower H hr (mem_powersetCard.mp hS).1
      (by rw [(mem_powersetCard.mp hS).2]))
  simp only [← mul_sum] at hsum
  rw [sum_survivingCount (G := G) index hrk] at hsum
  simpa only [sum_const,card_powersetCard,smul_eq_mul,
    Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hsum

/-- Full counting in a denominator-free polynomial form. The finite sample
space is nonempty, and its positive binomial cardinality is cancelled. -/
theorem full_counting_polynomial [Nonempty V] {index : Sym2 V → ℕ}
    (H : MatchingLabels G index) {r : ℕ} (hr : 0 < r)
    (hm : Fintype.card V * r ≤ G.edgeFinset.card) :
    (Fintype.card V*r) * (G.edgeFinset.card+1-r)^r <
      2 * monotoneCount G index r * (Fintype.card V*r)^r := by
  have hrk : r ≤ Fintype.card V*r := Nat.le_mul_of_pos_left r Fintype.card_pos
  have hrm : r ≤ G.edgeFinset.card := hrk.trans hm
  have hpow : 0 < (G.edgeFinset.card+1-r)^r := Nat.pow_pos (by omega)
  have hcount := full_counting_binomial H hr hm
  have hsurv := choose_survival_bound (m := G.edgeFinset.card) hrk
  have hbinom : 0 < G.edgeFinset.card.choose (Fintype.card V*r) := Nat.choose_pos hm
  have hlt := Nat.mul_lt_mul_of_pos_right hcount hpow
  have hle := Nat.mul_le_mul_left (2 * monotoneCount G index r) hsurv
  apply (Nat.mul_lt_mul_left hbinom).mp
  calc
    _ = ((Fintype.card V*r) * G.edgeFinset.card.choose (Fintype.card V*r)) *
      (G.edgeFinset.card+1-r)^r := by ring
    _ < (2 * monotoneCount G index r *
      (G.edgeFinset.card-r).choose (Fintype.card V*r-r)) *
      (G.edgeFinset.card+1-r)^r := hlt
    _ ≤ _ := by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hle

/-- Combine actual dispersion and full counting. No path-count hypothesis is
supplied: both inequalities have been constructed from the graph model. -/
theorem parallelGreedy_density_polynomial [Nonempty V] {index : Sym2 V → ℕ}
    {s r : ℕ} (H : IsParallelGreedy G index s) (hr : 0 < r)
    (hrs : 2*r ≤ s+1) (hm : Fintype.card V*r ≤ G.edgeFinset.card) :
    r * (G.edgeFinset.card+1-r)^r <
      2 * Fintype.card V * (Fintype.card V*r)^r := by
  have hlo := full_counting_polynomial H.matching hr hm
  have hhi := monotoneCount_le_square H hrs
  have hb := (Nat.mul_le_mul_left 2 hhi)
  have hc := Nat.mul_le_mul_right ((Fintype.card V*r)^r) hb
  have h := hlo.trans_le hc
  apply (Nat.mul_lt_mul_left (Fintype.card_pos (α := V))).mp
  simpa only [pow_two,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

end LengthExpander
