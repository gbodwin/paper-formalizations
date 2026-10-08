import LinearDistancePreservers.WeightedNativeForcing
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin

/-! Exact-size padding of weighted lower-bound witnesses. Injective graph
maps add isolated vertices; enlarging the terminal set retains every old
distance constraint. Distances are the original list-walk infima. -/
namespace LinearDistancePreservers.PreserverPadding
open SimpleGraph Finset WeightedDigraph WeightedNativeForcing ConsistentTiebreaking
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def Rigid (G : SimpleGraph V) (w : V → V → ℝ≥0) (S : Finset V) : Prop :=
  ∀ H : SimpleGraph V, H ≤ G →
    (∀ s ∈ S, ∀ t ∈ S,
      distance H.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
        distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t) → H = G

theorem realCost_map {G : SimpleGraph V} {K : SimpleGraph W}
    (f : G →g K) (w : W → W → ℝ≥0) {s t : V} (p : G.Walk s t) :
    realCost w (p.map f) = realCost (fun u v => w (f u) (f v)) p := by
  induction p with
  | nil => simp [realCost]
  | cons h p ih => simpa [realCost,Walk.map_cons,Walk.darts_cons] using ih

theorem distance_le_of_hom {G : SimpleGraph V} {K : SimpleGraph W}
    (f : G →g K) (w : W → W → ℝ≥0) (s t : V) :
    distance K.Adj (fun u v => (w u v : ℝ≥0∞)) (f s) (f t) ≤
      distance G.Adj (fun u v => (w (f u) (f v) : ℝ≥0∞)) s t := by
  apply le_sInf
  rintro c ⟨l,hl,rfl⟩
  obtain ⟨p,rfl⟩ := native_of_list_walk hl
  have hle := distance_le_cost (w := fun u v => (w u v : ℝ≥0∞))
    (support_isWalk (p := p.map f) (fun d _ => d.adj))
  apply hle.trans_eq
  rw [cost_support,cost_support]
  exact congrArg ENNReal.ofReal (realCost_map f w p)

variable (f : V ↪ W) (g : W → V) (hg : Function.LeftInverse g f)

def backHom {G : SimpleGraph V} {H : SimpleGraph W} (hH : H ≤ G.map f) :
    H →g H.comap f where
  toFun := g
  map_rel' := by
    intro u v h
    obtain ⟨a,b,hab,ha,hb⟩ := (map_adj f G u v).mp (hH h)
    change H.Adj (f (g u)) (f (g v))
    simpa only [← ha,← hb,hg a,hg b] using h

include hg in
/-- Every subgraph of the padded graph has exactly the same old-vertex
distances as its pullback. No shortest-path choice is assumed. -/
theorem distance_comap {G : SimpleGraph V} {H : SimpleGraph W}
    (hH : H ≤ G.map f) (w : V → V → ℝ≥0) (s t : V) :
    distance H.Adj (fun u v => (w (g u) (g v) : ℝ≥0∞)) (f s) (f t) =
      distance (H.comap f).Adj (fun u v => (w u v : ℝ≥0∞)) s t := by
  have hgf : ∀ u, g (f u) = u := hg
  apply le_antisymm
  · have hh := distance_le_of_hom (Hom.comap f H) (fun u v => w (g u) (g v)) s t
    change distance H.Adj (fun u v => (w (g u) (g v) : ℝ≥0∞)) (f s) (f t) ≤
      distance (H.comap f).Adj (fun u v => (w (g (f u)) (g (f v)) : ℝ≥0∞)) s t at hh
    simpa only [hgf] using hh
  · have hh := distance_le_of_hom (backHom f g hg hH) w (f s) (f t)
    change distance (H.comap f).Adj (fun u v => (w u v : ℝ≥0∞)) (g (f s)) (g (f t)) ≤
      distance H.Adj (fun u v => (w (g u) (g v) : ℝ≥0∞)) (f s) (f t) at hh
    simpa only [hgf] using hh

include hg in
theorem rigid_map {G : SimpleGraph V} {w : V → V → ℝ≥0} {S : Finset V}
    (hG : Rigid G w S) : Rigid (G.map f) (fun u v => w (g u) (g v)) (S.map f) := by
  intro H hH hp
  have hpull : H.comap f ≤ G := by
    intro u v huv
    exact (map_adj_apply).mp (hH huv)
  have heq : H.comap f = G := hG _ hpull (by
    intro s hs t ht
    have hh := hp (f s) (mem_map.mpr ⟨s,hs,rfl⟩) (f t) (mem_map.mpr ⟨t,ht,rfl⟩)
    rw [distance_comap f g hg hH, distance_comap f g hg le_rfl,
      comap_map_eq] at hh
    exact hh)
  exact le_antisymm hH (map_le_iff_le_comap.mpr (by rw [heq]))

theorem rigid_mono_terminals {G : SimpleGraph V} {w : V → V → ℝ≥0} {S T : Finset V}
    (hG : Rigid G w S) (hST : S ⊆ T) : Rigid G w T := by
  intro H hH hp
  exact hG H hH (fun s hs t ht => hp s (hST hs) t (hST ht))

/-- Pad to exactly N vertices and exactly T terminals, preserving the
entire forced edge count and positivity/symmetry of every graph edge. -/
theorem pad [Nonempty V] (G : SimpleGraph V) (w : V → V → ℝ≥0) (S : Finset V)
    (hG : Rigid G w S) (hw : ∀ u v, G.Adj u v → 0 < w u v ∧ w u v = w v u)
    {N T : ℕ} (hN : Fintype.card V ≤ N) (hT : S.card ≤ T) (hTN : T ≤ N) :
    ∃ (K : SimpleGraph (Fin N)) (w' : Fin N → Fin N → ℝ≥0) (S' : Finset (Fin N)),
      S'.card = T ∧ Rigid K w' S' ∧ K.edgeFinset.card = G.edgeFinset.card ∧
      ∀ u v, K.Adj u v → 0 < w' u v ∧ w' u v = w' v u := by
  classical
  let f : V ↪ Fin N := (Function.Embedding.nonempty_of_card_le (by simpa using hN)).some
  let g : Fin N → V := Function.invFun f
  have hg : Function.LeftInverse g f := Function.leftInverse_invFun f.injective
  obtain ⟨S',hS,_,hcard⟩ := exists_subsuperset_card_eq (subset_univ (S.map f))
    (by simpa using hT) (by simpa using hTN)
  refine ⟨G.map f,fun u v => w (g u) (g v),S',hcard,
    rigid_mono_terminals (rigid_map f g hg hG) hS,?_,?_⟩
  · convert card_edgeFinset_map f G using 1
    congr 1
    ext e
    simp only [mem_edgeFinset]
  · intro u v huv
    obtain ⟨a,b,hab,rfl,rfl⟩ := (map_adj f G u v).mp huv
    simpa only [hg a,hg b] using hw a b hab

end LinearDistancePreservers.PreserverPadding
