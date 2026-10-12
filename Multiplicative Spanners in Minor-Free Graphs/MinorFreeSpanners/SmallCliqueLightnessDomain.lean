import MinorFreeSpanners.PositiveEdgeMinorLightness
import MinorFreeSpanners.SmallMinors

/-! On a nontrivial connected graph, excluding a positive-order clique
already forces its order to be at least three. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners

 theorem nontrivial_connected_clique_order {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : ℕ) (hh : 0<h) (hn : 2≤Fintype.card V)
    (hc : G.Connected) (hf : CliqueMinorFree G h) : 3≤h := by
  by_contra he
  have casesH : h=1 ∨ h=2 := by omega
  rcases casesH with rfl|rfl
  · obtain ⟨v⟩ := hc.nonempty
    let emb : Fin 1 ↪ V := ⟨fun _ => v,fun _ _ _ => Subsingleton.elim _ _⟩
    exact hf ⟨MinorModel.ofEmbedding _ G emb (by intro i j hij; exact (hij.ne (Subsingleton.elim i j)).elim)⟩
  · have hb := (cliqueMinorFree_two_iff G).mp hf
    have hs : Subsingleton V := (connected_bot_iff.mp (hb ▸ hc)).1
    have hcard := Fintype.card_le_one_iff_subsingleton.mpr hs
    omega

end MinorFreeSpanners
