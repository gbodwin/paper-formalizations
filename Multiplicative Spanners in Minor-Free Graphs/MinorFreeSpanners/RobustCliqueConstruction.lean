import MinorFreeSpanners.ResidualConnectedCover
import MinorFreeSpanners.ExtendCliqueModel

/-! Construct the complete minor one actual connected branch at a time. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
attribute [local instance] Classical.propDecidable

theorem robust_core_clique_minor (G : SimpleGraph V) (D h : ℕ) (hD : 0 < D)
    (hsize : Fintype.card V ≤ 12*D) (hdeg : ∀ x, 4*D ≤ G.degree x)
    (hrob : DeletionConnected G (2*D))
    (hbudget : h*(48*(Nat.log 2 (Fintype.card V)+1)) ≤ D) :
    Nonempty (MinorModel (⊤ : SimpleGraph (Fin h)) G) := by
  classical
  let L := 48*(Nat.log 2 (Fintype.card V)+1)
  have build : ∀ r : ℕ, r ≤ h → ∃ S : Finset V, S.card ≤ r*L ∧
      ∃ M : MinorModel (⊤ : SimpleGraph (Fin r)) G,
        (∀ i, M.branch i ⊆ (S:Set V)) ∧
        ∀ i x, x ∉ S → ∃ y ∈ M.branch i, G.Adj y x := by
    intro r
    induction r with
    | zero =>
      intro _
      let M : MinorModel (⊤ : SimpleGraph (Fin 0)) G :=
        MinorModel.ofEmbedding _ G ⟨Fin.elim0,fun i => i.elim0⟩ (fun i => i.elim0)
      exact ⟨∅,by simp,M,(fun i => i.elim0),(fun i => i.elim0)⟩
    | succ r ih =>
      intro hr
      obtain ⟨S,hS,M,hinside,hdom⟩ := ih (by omega)
      have hSD : S.card ≤ D := hS.trans ((Nat.mul_le_mul_right L (by omega : r ≤ h)).trans hbudget)
      obtain ⟨C,hCne,hCS,hC,hCdom,hCconn⟩ :=
        exists_residual_connected_cover G D hD hsize hdeg hrob S hSD
      let M' := extendCliqueModel M S C hinside hdom hCne hCS hCconn
      refine ⟨C ∪ S,?_,M',?_,?_⟩
      · have hc := Finset.card_union_le C S
        dsimp [L] at hS ⊢
        nlinarith
      · intro i
        induction i using Fin.cases with
        | zero =>
          intro x hx
          exact Finset.mem_union.mpr (Or.inl hx)
        | succ i =>
          intro x hx
          exact Finset.mem_union.mpr (Or.inr (hinside i hx))
      · intro i x hx
        have hxS : x ∉ S := fun h => hx (Finset.mem_union.mpr (Or.inr h))
        induction i using Fin.cases with
        | zero => exact hCdom x hxS
        | succ i => exact hdom i x hxS
  obtain ⟨_,_,M,_,_⟩ := build h le_rfl
  exact ⟨M⟩

end MinorFreeSpanners
