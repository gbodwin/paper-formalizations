import LightSpanners.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Push

namespace LightSpanners
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]

def edgeGraph (E : Finset (Sym2 V)) : SimpleGraph V := fromEdgeSet (E : Set (Sym2 V))

@[simp] theorem mem_edgeGraph (E : Finset (Sym2 V)) (e : Sym2 V) :
    e ∈ (edgeGraph E).edgeSet ↔ e ∈ E ∧ ¬ e.IsDiag := by
  simp [edgeGraph, edgeSet_fromEdgeSet, Sym2.diagSet]

theorem edgeGraph_mono {E D : Finset (Sym2 V)} (h : E ⊆ D) :
    edgeGraph E ≤ edgeGraph D := fromEdgeSet_mono h

/-- Algorithm 1. Recursion processes the tail first, so supply a list in
nonincreasing weight order to process edges in nondecreasing weight order. -/
noncomputable def greedyEdges (w : Sym2 V → ℝ) (t : ℝ) :
    List (Sym2 V) → Finset (Sym2 V)
  | [] => ∅
  | e :: es => by
    classical
    exact let E := greedyEdges w t es
      if Covered (edgeGraph E) w t e then E else insert e E

theorem greedyEdges_subset (w : Sym2 V → ℝ) (t : ℝ) (l : List (Sym2 V)) :
    greedyEdges w t l ⊆ l.toFinset := by
  classical
  induction l with
  | nil => simp [greedyEdges]
  | cons e es ih =>
    simp only [greedyEdges]
    split_ifs
    · exact ih.trans (by simp)
    · exact insert_subset (by simp) (ih.trans (by simp))

theorem greedyEdges_covered (w : Sym2 V → ℝ) (t : ℝ) (ht : 1 ≤ t)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∀ e ∈ l, Covered (edgeGraph (greedyEdges w t l)) w t e := by
  classical
  induction l with
  | nil => simp
  | cons e es ih =>
    have hi := ih (fun d hd => hl d (by simp [hd]))
    intro d hd
    simp only [greedyEdges]
    split_ifs with hc
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hi d hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact covered_of_mem ht hw ((mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _, hl d (by simp)⟩)
      · exact covered_mono (edgeGraph_mono (subset_insert _ _)) (hi d hd)

/-- The actual greedy construction satisfies the walk definition of stretch. -/
theorem greedy_isSpanner (w : Sym2 V → ℝ) (t : ℝ) (ht : 1 ≤ t)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    IsSpanner (edgeGraph l.toFinset) (edgeGraph (greedyEdges w t l)) w t := by
  apply covered_edges_spanner (edgeGraph_mono (greedyEdges_subset w t l))
  intro e he
  exact greedyEdges_covered w t ht hw l hl e (List.mem_toFinset.mp ((mem_edgeGraph _ _).mp he).1)

theorem not_covered_witness {H : SimpleGraph V} {w : Sym2 V → ℝ} {t : ℝ}
    {e : Sym2 V} (h : ¬ Covered H w t e) :
    ∀ u v, s(u,v) = e → ∀ p : H.Walk u v, t * w e < walkWeight w p := by
  classical
  simp only [Covered] at h
  push Not at h
  obtain ⟨u,v,he,hbad⟩ := h
  intro a b hab p
  rcases Sym2.eq_iff.mp (hab.trans he.symm) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hbad p
  · simpa [walkWeight] using hbad p.reverse

/-- The induction step in the last-edge argument of Lemma 3.2. -/
theorem girth_insert (E : Finset (Sym2 V)) (w : Sym2 V → ℝ) (t : ℝ)
    (ht : 0 ≤ t + 1) (e : Sym2 V) (hmax : ∀ d ∈ E, w d ≤ w e)
    (hG : WeightedGirthAbove (edgeGraph E) w (t+1))
    (hc : ¬ Covered (edgeGraph E) w t e) :
    WeightedGirthAbove (edgeGraph (insert e E)) w (t+1) := by
  intro a p hp d hd
  by_cases hep : e ∈ p.edges
  · obtain ⟨u,v,heq,q,hqw,hqe⟩ := cycle_complement p hp w hep
    have hqold : ∀ x ∈ q.edges, x ∈ (edgeGraph E).edgeSet := by
      intro x hx
      obtain ⟨hxp,hxne⟩ := hqe x hx
      obtain ⟨hxi,hndi⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hxp)
      exact (mem_edgeGraph _ _).mpr ⟨(mem_insert.mp hxi).resolve_left hxne,hndi⟩
    have hbad := not_covered_witness hc v u (Sym2.eq_swap.trans heq.symm)
      (q.transfer (edgeGraph E) hqold)
    simp only [walkWeight_transfer] at hbad
    have hdmax : w d ≤ w e := by
      obtain ⟨hdi,_⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hd)
      rcases mem_insert.mp hdi with rfl | hdold
      · exact le_rfl
      · exact hmax d hdold
    have hmul := mul_le_mul_of_nonneg_left hdmax ht
    nlinarith
  · have hold : ∀ x ∈ p.edges, x ∈ (edgeGraph E).edgeSet := by
      intro x hx
      obtain ⟨hxi,hndi⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hx)
      have hxe : x ≠ e := fun h => hep (h ▸ hx)
      exact (mem_edgeGraph _ _).mpr ⟨(mem_insert.mp hxi).resolve_left hxe,hndi⟩
    have hcycle := hp.transfer hold
    simpa using hG a (p.transfer (edgeGraph E) hold) hcycle d (by simpa using hd)

/-- Lemma 3.2, proved for Algorithm 1 with arbitrary real stretch t ≥ -1.
`Pairwise` supplies the nondecreasing processing order, including weight ties. -/
theorem greedy_weightedGirth (w : Sym2 V → ℝ) (t : ℝ) (ht : 0 ≤ t+1)
    (l : List (Sym2 V)) (hs : l.Pairwise (fun a b => w b ≤ w a)) :
    WeightedGirthAbove (edgeGraph (greedyEdges w t l)) w (t+1) := by
  classical
  induction l with
  | nil =>
    intro a p hp e he
    have hh := p.edges_subset_edgeSet he
    simpa [greedyEdges] using hh
  | cons e es ih =>
    obtain ⟨hmax, hs⟩ := List.pairwise_cons.mp hs
    have old := ih hs
    simp only [greedyEdges]
    split_ifs with hc
    · exact old
    · exact girth_insert _ w t ht e
        (fun d hd => hmax d (List.mem_toFinset.mp (greedyEdges_subset w t es hd))) old hc
end LightSpanners
