import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Genuine graph-minor models: disjoint nonempty connected branch sets,
with a host edge for each model edge. Connectivity is witnessed by walks
inside the branch set. No minor-exclusion or density theorem is axiomatized. -/
namespace MinorFreeSpanners
open SimpleGraph

structure MinorModel {I V : Type*} (F : SimpleGraph I) (G : SimpleGraph V) where
  branch : I → Set V
  nonempty : ∀ i, (branch i).Nonempty
  disjoint : ∀ i j, i ≠ j → Disjoint (branch i) (branch j)
  connected : ∀ i u, u ∈ branch i → ∀ v, v ∈ branch i →
    ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∈ branch i
  adjacent : ∀ i j, F.Adj i j → ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v

namespace MinorModel
variable {I V : Type*} {F : SimpleGraph I} {G H : SimpleGraph V}

def mapSupergraph (M : MinorModel F G) (h : G ≤ H) : MinorModel F H where
  branch := M.branch
  nonempty := M.nonempty
  disjoint := M.disjoint
  connected := by
    intro i u hu v hv
    obtain ⟨p, hp⟩ := M.connected i u hu v hv
    exact ⟨p.mapLe h, by simpa using hp⟩
  adjacent := by
    intro i j hij
    obtain ⟨u, hu, v, hv, huv⟩ := M.adjacent i j hij
    exact ⟨u, hu, v, hv, h huv⟩
end MinorModel

def CliqueMinorFree {V : Type*} (G : SimpleGraph V) (h : ℕ) : Prop :=
  ¬ Nonempty (MinorModel (⊤ : SimpleGraph (Fin h)) G)

theorem CliqueMinorFree.mono {V : Type*} {G H : SimpleGraph V} {h : ℕ}
    (hG : CliqueMinorFree G h) (hHG : H ≤ G) : CliqueMinorFree H h := by
  rintro ⟨M⟩
  exact hG ⟨M.mapSupergraph hHG⟩

end MinorFreeSpanners

namespace MinorFreeSpanners
open SimpleGraph

/-- Disjoint nonempty branch sets inject the model vertices into the host.
This cardinality obstruction is sufficient for the K₄-free triangle example. -/
noncomputable def MinorModel.representative {I V : Type*} {F : SimpleGraph I}
    {G : SimpleGraph V} (M : MinorModel F G) (i : I) : V :=
  (M.nonempty i).choose

theorem MinorModel.representative_injective {I V : Type*} {F : SimpleGraph I}
    {G : SimpleGraph V} (M : MinorModel F G) :
    Function.Injective M.representative := by
  intro i j hij
  by_contra hne
  have hd := Set.disjoint_left.mp (M.disjoint i j hne)
  have hi : M.representative i ∈ M.branch i := (M.nonempty i).choose_spec
  have hj : M.representative j ∈ M.branch j := (M.nonempty j).choose_spec
  exact hd (hij ▸ hi) hj

theorem cliqueMinorFree_of_card_lt {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : ℕ) (hcard : Fintype.card V < h) : CliqueMinorFree G h := by
  rintro ⟨M⟩
  have := Fintype.card_le_of_injective _ M.representative_injective
  have hc : h ≤ Fintype.card V := by simpa using this
  exact not_le_of_gt hcard hc

end MinorFreeSpanners

namespace MinorFreeSpanners
open SimpleGraph

/-- Singleton branch sets lift every injective graph homomorphism to a
minor model. -/
def MinorModel.ofEmbedding {I V : Type*} (F : SimpleGraph I) (G : SimpleGraph V)
    (f : I ↪ V) (hf : ∀ i j, F.Adj i j → G.Adj (f i) (f j)) : MinorModel F G where
  branch := fun i => {f i}
  nonempty := fun i => ⟨f i, rfl⟩
  disjoint := by
    intro i j hij
    exact Set.disjoint_singleton.mpr (fun h => hij (f.injective h))
  connected := by
    intro i u hu v hv
    simp only [Set.mem_singleton_iff] at hu hv
    subst u; subst v
    exact ⟨.nil, by simp⟩
  adjacent := fun i j hij => ⟨f i, rfl, f j, rfl, hf i j hij⟩

end MinorFreeSpanners
