import MinorFreeSpanners.IsolatedPadding

/-! Finite lower-bound amplification to every requested vertex count at least
that of the core. The graph construction and its quantitative size are proved;
existence of a dense high-girth core remains a separate input. -/
namespace MinorFreeSpanners
open SimpleGraph
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Rounding down the number of disjoint copies loses at most a factor two. -/
theorem copies_cover_half (n v : ℕ) (hv : 0 < v) (hn : v ≤ n) :
    n ≤ 2 * ((n / v) * v) := by
  have hq : 1 ≤ n / v := (Nat.le_div_iff_mul_le hv).mpr (by simpa using hn)
  have hr := Nat.mod_lt n hv
  have he := Nat.div_add_mod n v
  rw [Nat.mul_comm v (n/v)] at he
  have hprod : v ≤ n / v * v := by nlinarith
  omega

/-- A concrete exact-size graph: disjoint core copies and isolated remainder
vertices. This is a sparsity construction and makes no disconnected-MST claim. -/
def exactSizeGraph (G : SimpleGraph V) (n : ℕ) :
    SimpleGraph ((Fin (n / Fintype.card V) × V) ⊕ Fin (n % Fintype.card V)) :=
  padGraph (copyGraph (Fin (n / Fintype.card V)) G) (Fin (n % Fintype.card V))

omit [DecidableEq V] in
theorem exactSizeGraph_card (n : ℕ) :
    Fintype.card ((Fin (n / Fintype.card V) × V) ⊕ Fin (n % Fintype.card V)) = n := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  simpa only [Nat.mul_comm] using Nat.div_add_mod n (Fintype.card V)

theorem exactSizeGraph_edge_count (G : SimpleGraph V) (n : ℕ) :
    (exactSizeGraph G n).edgeFinset.card = (n / Fintype.card V) * G.edgeFinset.card := by
  unfold exactSizeGraph
  rw [padGraph.edge_count, copyGraph.edge_count, Fintype.card_fin]

/-- Given an actual high-girth core with fewer than choose(h,2) edges, construct
an exactly n-vertex K_h-minor-free graph on which every (2k−1)-spanner retains
at least n times the core's edge/vertex ratio, up to the explicit factor two. -/
theorem exact_size_core_lower_bound (G : SimpleGraph V) (n k h : ℕ)
    (hv : 0 < Fintype.card V) (hn : Fintype.card V ≤ n) (hh : 2 ≤ h)
    (hm : G.edgeFinset.card < h.choose 2) (hg : GirthAbove G (2*k)) :
    CliqueMinorFree (exactSizeGraph G n) h ∧
    GirthAbove (exactSizeGraph G n) (2*k) ∧
    ∀ H : SimpleGraph ((Fin (n / Fintype.card V) × V) ⊕ Fin (n % Fintype.card V)),
      LightSpanners.IsSpanner (exactSizeGraph G n) H (fun _ => 1) (2*k-1) →
      H = exactSizeGraph G n ∧
      n * G.edgeFinset.card ≤ 2 * Fintype.card V * H.edgeFinset.card := by
  have hminor : CliqueMinorFree (exactSizeGraph G n) h :=
    padGraph.minorFree h hh (copyGraph.minorFree h (by omega) (cliqueMinorFree_of_edges G h hm))
  have hgirth : GirthAbove (exactSizeGraph G n) (2*k) := padGraph.girth (copyGraph.girth hg)
  refine ⟨hminor,hgirth,?_⟩
  intro H hH
  have he := high_girth_spanner_eq k hgirth hH
  subst H
  refine ⟨rfl,?_⟩
  rw [exactSizeGraph_edge_count]
  have hb := Nat.mul_le_mul_right G.edgeFinset.card (copies_cover_half n (Fintype.card V) hv hn)
  nlinarith [hb]

end MinorFreeSpanners
