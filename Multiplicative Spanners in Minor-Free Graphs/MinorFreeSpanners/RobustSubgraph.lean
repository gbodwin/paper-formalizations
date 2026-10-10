import MinorFreeSpanners.InducedDegreeBudget
import MinorFreeSpanners.FiniteSeparatedSide

/-! The actual deterministic separator step from the clique-minor proof.
The graph is either already robust or an explicit induced side is robust. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem robust_or_small_robust_induced (G : SimpleGraph V) (D : ℕ)
    (hsize : Fintype.card V ≤ 12*D) (hdegree : ∀ x, 6*D ≤ G.degree x) :
    DeletionConnected G (2*D) ∨
      ∃ A : Finset V, A.Nonempty ∧ A.card ≤ 6*D ∧
        Nonempty (MinorModel (G.induce (A:Set V)) G) ∧
        (∀ x : A, 4*D ≤ (G.induce (A:Set V)).degree x) ∧
        DeletionConnected (G.induce (A:Set V)) (2*D) := by
  classical
  by_cases hrobust : DeletionConnected G (2*D)
  · exact Or.inl hrobust
  · obtain ⟨S,A,hS,hA,_,hhalf,horizon⟩ := exists_separator_side G (2*D) hrobust
    have hsmall : A.card ≤ 6*D := by omega
    obtain ⟨hmin,hconn⟩ := small_separator_side_robust G A S D
      (fun x _ => hdegree x) hsmall (by omega) horizon
    exact Or.inr ⟨A,hA,hsmall,
      ⟨MinorModel.ofEmbedding _ G (Function.Embedding.subtype _) (fun _ _ h => h)⟩,
      hmin,hconn⟩

end MinorFreeSpanners
