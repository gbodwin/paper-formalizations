import BodwinPapers.VFTSpanners.FiniteBound
import Mathlib.Data.Finset.Lattice.Fold

namespace BodwinPapers.VFTSpanners
open SimpleGraph Finset

/-- No simple cycle has at most `k` edges; forests satisfy this for every `k`. -/
def HighGirth {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ a, ∀ p : G.Walk a a, p.IsCycle → k < p.length

/-- The paper's extremal function: maximum number of edges of a simple
undirected graph on exactly `n` vertices with girth strictly greater than `k`. -/
noncomputable def extremalEdges (n k : ℕ) : ℕ := by
  classical
  exact ((univ : Finset (SimpleGraph (Fin n))).filter (fun G => HighGirth G k)).sup
    (fun G => G.edgeFinset.card)

attribute [local instance] Classical.propDecidable

theorem edge_count_le_extremal {V : Type*} [Fintype V] (G : SimpleGraph V)
    (n k : ℕ) (hn : Fintype.card V = n) (hg : HighGirth G k) :
    G.edgeFinset.card ≤ extremalEdges n k := by
  classical
  let H := G.overFin hn
  let i := G.overFinIso hn
  have hH : HighGirth H k := by
    intro a p hp
    have h := hg (i.symm a) (p.map i.symm.toHom) (hp.map i.symm.injective)
    simpa using h
  have hle : H.edgeFinset.card ≤ extremalEdges n k := by
    unfold extremalEdges
    convert (Finset.le_sup (f := fun (K : SimpleGraph (Fin n)) => K.edgeFinset.card)
      (mem_filter.mpr ⟨mem_univ H,hH⟩) : _ ≤
        ((univ : Finset (SimpleGraph (Fin n))).filter (fun K => HighGirth K k)).sup
          (fun K => K.edgeFinset.card)) using 1
  rw [i.card_edgeFinset_eq]
  exact hle

theorem one_le_extremal_two (k : ℕ) : 1 ≤ extremalEdges 2 k := by
  classical
  let G : SimpleGraph (Fin 2) := ⊤
  have hc : G.edgeFinset.card = 1 := by
    change (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1
    rw [card_edgeFinset_top_eq_card_choose_two]
    decide
  have hg : HighGirth G k := by
    intro a p hp
    have h1 := hp.isTrail.length_le_card_edgeFinset
    have h3 := hp.isCircuit.three_le_length
    rw [hc] at h1
    omega
  have h := edge_count_le_extremal G 2 k (by simp) hg
  convert h using 1
  convert hc.symm using 2; ext e; simp

/-- A complete finite form of the counting implication in Theorem 1.
The `max 2` convention makes the dense-fault and empty-graph cases precise. -/
theorem blocking_extremal_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset (V × Sym2 V)) (k f : ℕ)
    (hf : 1 ≤ f) (hB : IsBlockingSet G k (B : Set (V × Sym2 V)))
    (hb : B.card ≤ f*G.edgeFinset.card) :
    G.edgeFinset.card ≤ 36*f^2 * extremalEdges (max 2 (Fintype.card V / (2*f))) k := by
  by_cases hn : 6*f ≤ Fintype.card V
  · obtain ⟨S,hS,hcount,hg⟩ := exists_high_girth_sample_finite G B k f hf hn hB hb
    have hr : 3 ≤ Fintype.card V / (2*f) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hb' := edge_count_le_extremal
      (prunedGraph G (S : Set V) (B : Set (V × Sym2 V)))
      (Fintype.card V / (2*f)) k (by simpa using hS) hg
    rw [max_eq_right (by omega)]
    have h := Nat.mul_le_mul_left (32*f^2) hb'
    nlinarith
  · have hnlt : Fintype.card V < 6*f := by omega
    have hr : Fintype.card V / (2*f) ≤ 2 := by
      have h : Fintype.card V / (2*f) < 3 :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < 2*f)).mpr (by omega)
      omega
    rw [max_eq_left hr]
    have h1 := one_le_extremal_two k
    have hc := G.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_two_right] at hc
    have hd := Nat.div_le_self (Fintype.card V * (Fintype.card V - 1)) 2
    have hp := Nat.mul_le_mul_left (Fintype.card V) (Nat.sub_le (Fintype.card V) 1)
    have hn2 := Nat.mul_self_le_mul_self (Nat.le_of_lt hnlt)
    have hh := Nat.mul_le_mul_left (36*f^2) h1
    nlinarith

end BodwinPapers.VFTSpanners
