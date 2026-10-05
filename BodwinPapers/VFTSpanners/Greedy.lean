import BodwinPapers.VFTSpanners.Weighted
import BodwinPapers.VFTSpanners.Sampling
import Mathlib.Tactic.Push
import Mathlib.Data.List.Sort

namespace BodwinPapers.VFTSpanners
open SimpleGraph Finset
variable {V : Type*}

/-- The graph with exactly these non-loop edge labels. -/
def edgeGraph (E : Finset (Sym2 V)) : SimpleGraph V := fromEdgeSet (E : Set (Sym2 V))

@[simp] theorem mem_edgeGraph (E : Finset (Sym2 V)) (e : Sym2 V) :
    e ∈ (edgeGraph E).edgeSet ↔ e ∈ E ∧ ¬ e.IsDiag := by
  simp [edgeGraph, edgeSet_fromEdgeSet, Sym2.diagSet]

theorem edgeGraph_mono {E D : Finset (Sym2 V)} (h : E ⊆ D) :
    edgeGraph E ≤ edgeGraph D := fromEdgeSet_mono h

variable [DecidableEq V]

/-- Algorithm 1, processing the list from right to left. A list in descending
weight order therefore processes edges in nondecreasing weight order. The
classical edge test is the exact mathematical test, not an efficient implementation. -/
noncomputable def greedyEdges (w : Sym2 V → ℝ) (k f : ℕ) :
    List (Sym2 V) → Finset (Sym2 V)
  | [] => ∅
  | e :: es => by
    classical
    exact let E := greedyEdges w k f es
      if Covered (edgeGraph E) w k f e then E else insert e E

theorem greedyEdges_subset (w : Sym2 V → ℝ) (k f : ℕ) (l : List (Sym2 V)) :
    greedyEdges w k f l ⊆ l.toFinset := by
  classical
  induction l with
  | nil => simp [greedyEdges]
  | cons e es ih =>
    simp only [greedyEdges]
    split_ifs
    · exact ih.trans (by simp)
    · exact insert_subset (by simp) (ih.trans (by simp))

theorem greedyEdges_covered (w : Sym2 V → ℝ) (k f : ℕ) (hk : 1 ≤ k)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V)) (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∀ e ∈ l, Covered (edgeGraph (greedyEdges w k f l)) w k f e := by
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
      · exact covered_of_mem hk hw ((mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _, hl d (by simp)⟩)
      · exact covered_mono (edgeGraph_mono (subset_insert _ _)) (hi d hd)

/-- Failure of the exact greedy test produces a fault witness, independent
of which orientation of the undirected edge is used. -/
theorem not_covered_witness {H : SimpleGraph V} {w : Sym2 V → ℝ} {k f : ℕ}
    {e : Sym2 V} (h : ¬ Covered H w k f e) :
    ∃ F : Finset V, F.card ≤ f ∧ (∀ x ∈ F, x ∉ e) ∧
      ∀ u v, s(u,v) = e → ∀ p : H.Walk u v,
        Avoids F p → (k : ℝ)*w e < walkWeight w p := by
  classical
  simp only [Covered] at h
  push Not at h
  obtain ⟨u,v,he,F,hF,hu,hv,hbad⟩ := h
  refine ⟨F,hF,?_,?_⟩
  · intro x hx
    rw [← he]
    simp only [Sym2.mem_iff]
    rintro (rfl | rfl) <;> contradiction
  · intro a b hab p hp
    rcases Sym2.eq_iff.mp (hab.trans he.symm) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hbad p hp
    · have hrev : Avoids F p.reverse := by simpa [Avoids] using hp
      simpa [walkWeight] using hbad p.reverse hrev

/-- Adding an edge that fails the greedy test extends the blocking set by
at most one fault witness per fault vertex. -/
theorem extend_blocking (E : Finset (Sym2 V)) (B : Finset (V × Sym2 V))
    (w : Sym2 V → ℝ) (k f : ℕ) (e : Sym2 V)
    (he : ¬ e.IsDiag) (hne : e ∉ E) (hw : 0 ≤ w e)
    (hmax : ∀ d ∈ E, w d ≤ w e)
    (hB : IsBlockingSet (edgeGraph E) (k+1) (B : Set (V × Sym2 V)))
    (hb : B.card ≤ f*E.card) (hc : ¬ Covered (edgeGraph E) w k f e) :
    ∃ C : Finset (V × Sym2 V),
      IsBlockingSet (edgeGraph (insert e E)) (k+1) (C : Set (V × Sym2 V)) ∧
      C.card ≤ f*(insert e E).card := by
  classical
  obtain ⟨F,hF,hend,hbad⟩ := not_covered_witness hc
  let C := B ∪ F ×ˢ {e}
  have hmono : edgeGraph E ≤ edgeGraph (insert e E) := edgeGraph_mono (subset_insert _ _)
  refine ⟨C,⟨?_,?_⟩,?_⟩
  · intro x d hxd
    rcases mem_union.mp hxd with hxd | hxd
    · obtain ⟨hed,hnot⟩ := hB.1 hxd
      exact ⟨(edgeSet_mono hmono) hed, hnot⟩
    · obtain ⟨hx,hd⟩ := mem_product.mp hxd
      have hd' : d = e := mem_singleton.mp hd
      subst d
      exact ⟨(mem_edgeGraph _ _).mpr ⟨mem_insert_self _ _,he⟩, hend x hx⟩
  · intro a p hp hlen
    by_cases hep : e ∈ p.edges
    · obtain ⟨u,v,huv,q,hqlen,hqe,hqv⟩ := cycle_complement p hp hep
      have hqold : ∀ d ∈ q.edges, d ∈ (edgeGraph E).edgeSet := by
        intro d hd
        obtain ⟨hdp,hdne⟩ := hqe d hd
        obtain ⟨hdi,hndi⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hdp)
        exact (mem_edgeGraph _ _).mpr ⟨(mem_insert.mp hdi).resolve_left hdne,hndi⟩
      let q' := q.transfer (edgeGraph E) hqold
      have hcost : walkWeight w q' ≤ (k : ℝ)*w e := by
        have hl : q.length ≤ k := by omega
        have hl' : (q.length : ℝ) ≤ k := by exact_mod_cast hl
        have hqw := walkWeight_le w q (w e) (fun d hd =>
          hmax d ((mem_edgeGraph _ _).mp (hqold d hd)).1)
        simp only [q', walkWeight_transfer]
        exact hqw.trans (mul_le_mul_of_nonneg_right hl' hw)
      have hinter : ∃ x ∈ q.support, x ∈ F := by
        by_contra hn
        push Not at hn
        have hav : Avoids F q' := by simpa [Avoids,q'] using hn
        have heq : s(v,u) = e := Sym2.eq_swap.trans huv.symm
        exact (not_lt_of_ge hcost) (hbad v u heq q' hav)
      obtain ⟨x,hx,hxF⟩ := hinter
      exact ⟨x,e,mem_union_right _ (mem_product.mpr ⟨hxF,mem_singleton_self _⟩),hqv x hx,hep⟩
    · have hold : ∀ d ∈ p.edges, d ∈ (edgeGraph E).edgeSet := by
        intro d hd
        obtain ⟨hdi,hndi⟩ := (mem_edgeGraph _ _).mp (p.edges_subset_edgeSet hd)
        have hde : d ≠ e := fun h => hep (h ▸ hd)
        exact (mem_edgeGraph _ _).mpr ⟨(mem_insert.mp hdi).resolve_left hde,hndi⟩
      have hcycle : (p.transfer (edgeGraph E) hold).IsCycle := hp.transfer hold
      obtain ⟨x,d,hxd,hx,hd⟩ := hB.2 (p.transfer (edgeGraph E) hold) hcycle (by simpa using hlen)
      exact ⟨x,d,mem_union_left _ hxd,by simpa using hx,by simpa using hd⟩
  · have hcard := card_union_le B (F ×ˢ {e})
    simp only [card_product, card_singleton, mul_one] at hcard
    rw [card_insert_of_notMem hne]
    change (B ∪ F ×ˢ {e}).card ≤ _
    nlinarith

/-- Lemma 3 for the actual recursive greedy algorithm and any tie ordering. -/
theorem greedy_blocking (w : Sym2 V → ℝ) (k f : ℕ)
    (hw : ∀ e, 0 ≤ w e) (l : List (Sym2 V))
    (hnd : l.Nodup) (hs : l.Pairwise (fun e d => w d ≤ w e))
    (hl : ∀ e ∈ l, ¬ e.IsDiag) :
    ∃ B : Finset (V × Sym2 V),
      IsBlockingSet (edgeGraph (greedyEdges w k f l)) (k+1) (B : Set (V × Sym2 V)) ∧
      B.card ≤ f*(greedyEdges w k f l).card := by
  classical
  induction l with
  | nil =>
    refine ⟨∅,⟨by simp,?_⟩,by simp [greedyEdges]⟩
    intro a p hp
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h p => simp [greedyEdges,edgeGraph] at h
  | cons e es ih =>
    obtain ⟨hne,hnd⟩ := List.nodup_cons.mp hnd
    obtain ⟨hmax,hs⟩ := List.pairwise_cons.mp hs
    obtain ⟨B,hB,hcard⟩ := ih hnd hs (fun d hd => hl d (by simp [hd]))
    simp only [greedyEdges]
    split_ifs with hc
    · exact ⟨B,hB,hcard⟩
    · apply extend_blocking _ B w k f e (hl e (by simp)) _ (hw e) _ hB hcard hc
      · exact fun he => hne (List.mem_toFinset.mp (greedyEdges_subset w k f es he))
      · intro d hd
        exact hmax d (List.mem_toFinset.mp (greedyEdges_subset w k f es hd))

end BodwinPapers.VFTSpanners
