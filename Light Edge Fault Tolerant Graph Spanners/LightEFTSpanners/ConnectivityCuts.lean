import LightEFTSpanners.MissingEdgeConnectivity

namespace LightEFTSpanners.ConnectivityCuts
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- An unordered pair crosses S exactly when it has an endpoint on each side. -/
def Crosses (S : Set V) (e : Sym2 V) : Prop :=
  (∃ a∈e,a∈S) ∧ ∃ b∈e,b∉S

omit [Fintype V] in
@[simp] theorem crosses_pair (S : Set V) (a b : V) :
    Crosses S s(a,b) ↔ (a∈S ∧ b∉S) ∨ (b∈S ∧ a∉S) := by
  simp only [Crosses,Sym2.mem_iff]
  aesop

/-- The actual finite edge cut of a vertex set, using the input edge identities. -/
noncomputable def edges (G : SimpleGraph V) (S : Set V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (Crosses S)

@[simp] theorem mem_edges_pair (G : SimpleGraph V) (S : Set V) (a b : V) :
    s(a,b)∈edges G S ↔ G.Adj a b ∧ ((a∈S ∧ b∉S) ∨ (b∈S ∧ a∉S)) := by
  simp [edges]

/-- No surviving edge crosses the vertex cut after all actual cut edges fail. -/
theorem after_cut_adj_sides (G : SimpleGraph V) (S : Set V) {a b : V}
    (h : (afterFaults G (edges G S)).Adj a b) : a∈S ↔ b∈S := by
  obtain ⟨hab,hnot⟩ := deleteEdges_adj.mp h
  have hn : ¬((a∈S ∧ b∉S) ∨ (b∈S ∧ a∉S)) :=
    fun hc => hnot ((mem_edges_pair G S a b).mpr ⟨hab,hc⟩)
  tauto

/-- Actual surviving walks remain entirely on one side of the vertex cut. -/
theorem after_cut_reachable_sides (G : SimpleGraph V) (S : Set V) {a b : V}
    (h : (afterFaults G (edges G S)).Reachable a b) : a∈S ↔ b∈S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hab p ih => exact (after_cut_adj_sides G S hab).trans ih

/-- Native edge connectivity gives the genuine cardinal lower bound on every
vertex cut separating the two specified terminals. -/
theorem edgeReachable_le_cut (G : SimpleGraph V) (S : Set V) {a b : V} {k : ℕ}
    (h : G.IsEdgeReachable k a b) (ha : a∈S) (hb : b∉S) : k≤(edges G S).card := by
  by_contra! hlt
  have he : (↑(edges G S) : Set (Sym2 V)).encard<k := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hlt
  exact hb ((after_cut_reachable_sides G S (h he)).mp ha)

/-- Conversely, genuine cardinal lower bounds on all separating vertex cuts
imply native set-based edge connectivity. The witness cut is an actual component
after the supplied edge failures; no max-flow or path-packing theorem is used. -/
theorem edgeReachable_of_cut_lower (G : SimpleGraph V) {a b : V} {k : ℕ}
    (hcut : ∀ S : Set V,a∈S → b∉S → k≤(edges G S).card) :
    G.IsEdgeReachable k a b := by
  classical
  intro faults hfaults
  by_contra hnot
  let S : Set V := {v | (G.deleteEdges faults).Reachable a v}
  have ha : a∈S := Reachable.refl _
  have hb : b∉S := hnot
  have hsub : edges G S ⊆ faults.toFinset := by
    intro e he
    rcases e with ⟨u,v⟩
    obtain ⟨huv,hcross⟩ := (mem_edges_pair G S u v).mp he
    by_contra hn
    have hnf : s(u,v)∉faults := by simpa using hn
    have hsurv : (G.deleteEdges faults).Adj u v := deleteEdges_adj.mpr ⟨huv,hnf⟩
    rcases hcross with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact hv (hu.trans hsurv.reachable)
    · exact hu (hv.trans hsurv.reachable.symm)
  have hlow := (hcut S ha hb).trans (card_le_card hsub)
  have hhigh : faults.toFinset.card<k := by
    rw [Set.encard_eq_coe_toFinset_card] at hfaults
    exact_mod_cast hfaults
  omega

theorem edgeReachable_iff_cut_lower (G : SimpleGraph V) {a b : V} {k : ℕ} :
    G.IsEdgeReachable k a b ↔ ∀ S : Set V,a∈S → b∉S → k≤(edges G S).card :=
  ⟨fun h S ha hb => edgeReachable_le_cut G S h ha hb,edgeReachable_of_cut_lower G⟩

/-- Actual cut cardinality is posimodular, the elementary uncrossing inequality
used in the external packing proof. No packing existence is assumed here. -/
theorem card_posimodular (G : SimpleGraph V) (S T : Set V) :
    (edges G (S\T)).card + (edges G (T\S)).card ≤
      (edges G S).card + (edges G T).card := by
  classical
  have hc (A : Set V) : (edges G A).card =
      ∑ e∈G.edgeFinset, if Crosses A e then 1 else 0 := by
    simp [edges]
  simp only [hc,← sum_add_distrib]
  apply sum_le_sum
  intro e _
  rcases e with ⟨a,b⟩
  simp only [crosses_pair,Set.mem_sdiff]
  by_cases haS : a∈S <;> by_cases hbS : b∈S <;>
    by_cases haT : a∈T <;> by_cases hbT : b∈T <;> simp_all
end LightEFTSpanners.ConnectivityCuts
