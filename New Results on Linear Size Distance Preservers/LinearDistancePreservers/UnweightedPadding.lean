import LinearDistancePreservers.PreserverPadding
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Padding unweighted subset-preserver lower bounds to arbitrary finite
vertex and terminal counts. All distances are mathlib's native `edist`. -/
namespace LinearDistancePreservers.UnweightedPadding
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def Rigid (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ H : SimpleGraph V, H ≤ G →
    (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) → H = G

theorem edist_le_of_hom {G : SimpleGraph V} {K : SimpleGraph W}
    (f : G →g K) (s t : V) : K.edist (f s) (f t) ≤ G.edist s t := by
  apply le_iInf
  intro p
  simpa only [Walk.length_map] using (p.map f).edist_le

variable (f : V ↪ W) (g : W → V) (hg : Function.LeftInverse g f)

include hg in
theorem edist_comap {G : SimpleGraph V} {H : SimpleGraph W}
    (hH : H ≤ G.map f) (s t : V) :
    H.edist (f s) (f t) = (H.comap f).edist s t := by
  have hgf : ∀ u, g (f u) = u := hg
  apply le_antisymm
  · exact edist_le_of_hom (Hom.comap f H) s t
  · have hh := edist_le_of_hom (PreserverPadding.backHom f g hg hH) (f s) (f t)
    change (H.comap f).edist (g (f s)) (g (f t)) ≤ H.edist (f s) (f t) at hh
    simpa only [hgf] using hh

include hg in
theorem rigid_map {G : SimpleGraph V} {S : Finset V}
    (hG : Rigid G S) : Rigid (G.map f) (S.map f) := by
  intro H hH hp
  have hpull : H.comap f ≤ G := by
    intro u v huv
    exact (map_adj_apply).mp (hH huv)
  have heq : H.comap f = G := hG _ hpull (by
    intro s hs t ht
    have hh := hp (f s) (mem_map.mpr ⟨s,hs,rfl⟩) (f t) (mem_map.mpr ⟨t,ht,rfl⟩)
    rw [edist_comap f g hg hH,edist_comap f g hg le_rfl,comap_map_eq] at hh
    exact hh)
  exact le_antisymm hH (map_le_iff_le_comap.mpr (by rw [heq]))

theorem rigid_mono_terminals {G : SimpleGraph V} {S T : Finset V}
    (hG : Rigid G S) (hST : S ⊆ T) : Rigid G T := by
  intro H hH hp
  exact hG H hH (fun s hs t ht => hp s (hST hs) t (hST ht))

/-- Add isolated vertices and enlarge the terminal set, without losing
any of the forced edges or changing any old distance. -/
theorem pad [Nonempty V] (G : SimpleGraph V) (S : Finset V)
    (hG : Rigid G S) {N T : ℕ}
    (hN : Fintype.card V ≤ N) (hT : S.card ≤ T) (hTN : T ≤ N) :
    ∃ (K : SimpleGraph (Fin N)) (S' : Finset (Fin N)),
      S'.card = T ∧ Rigid K S' ∧ K.edgeFinset.card = G.edgeFinset.card := by
  classical
  let f : V ↪ Fin N := (Function.Embedding.nonempty_of_card_le (by simpa using hN)).some
  let g : Fin N → V := Function.invFun f
  have hg : Function.LeftInverse g f := Function.leftInverse_invFun f.injective
  obtain ⟨S',hS,_,hcard⟩ := exists_subsuperset_card_eq (subset_univ (S.map f))
    (by simpa using hT) (by simpa using hTN)
  refine ⟨G.map f,S',hcard,rigid_mono_terminals (rigid_map f g hg hG) hS,?_⟩
  convert card_edgeFinset_map f G using 1
  congr 1
  ext e
  simp only [mem_edgeFinset]

end LinearDistancePreservers.UnweightedPadding
