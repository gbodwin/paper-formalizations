import MinorFreeSpanners.MinorHostTransport
import Mathlib.Basic.Real.Basic

/-! Reindex an actual bounded minor on a finite ordinal. This packages the
same graph and original host branches without changing density or width. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I J V : Type*} {F : SimpleGraph I} {G : SimpleGraph V}

noncomputable def reindex (M : MinorModel F G) (e : J ↪ I) :
    MinorModel (F.comap e) G where
  branch j := M.branch (e j)
  nonempty j := M.nonempty (e j)
  disjoint i j h := M.disjoint (e i) (e j) (fun he => h (e.injective he))
  connected j := M.connected (e j)
  adjacent i j h := M.adjacent (e i) (e j) h

theorem IsBounded.reindex [Fintype V] (M : MinorModel F G) (e : J ↪ I)
    {m : ℕ} (hM : M.IsBounded m) : (M.reindex e).IsBounded m := fun j => hM (e j)

end MinorModel

/-- Same positive graph cardinality, same density, and the same bounded
branch sets, with the target renamed to Fin n. -/
theorem exists_finite_bounded_dense_minor {I V : Type*} [Fintype I] [Fintype V]
    (F : SimpleGraph I) (G : SimpleGraph V) (m : ℕ) (d : ℝ)
    (M : MinorModel F G) (hM : M.IsBounded m)
    (hpos : 0 < Fintype.card I) (hd : d*Fintype.card I ≤ (F.edgeFinset.card:ℝ)) :
    ∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ N : MinorModel Q G,
      0 < n ∧ N.IsBounded m ∧ d*n ≤ (Q.edgeFinset.card:ℝ) := by
  classical
  let e := (Fintype.equivFin I).symm
  have he : (F.comap e).edgeFinset.card=F.edgeFinset.card :=
    (SimpleGraph.Iso.comap e F).card_edgeFinset_eq
  refine ⟨Fintype.card I,F.comap e,M.reindex e.toEmbedding,hpos,MinorModel.IsBounded.reindex M e.toEmbedding hM,?_⟩
  simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at he hd ⊢
  rwa [he]

end MinorFreeSpanners
