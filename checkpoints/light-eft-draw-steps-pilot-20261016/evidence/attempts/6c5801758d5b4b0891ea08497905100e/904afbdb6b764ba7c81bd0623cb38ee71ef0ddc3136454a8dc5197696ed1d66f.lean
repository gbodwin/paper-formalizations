import LightSpanners.Basic
import LightSpanners.MinimumTree
import Mathlib.Data.Finset.Card

/-! Actual edge-failure semantics. The walk replacement definition includes
unreachable pairs without imposing global connectedness on the input graph. -/
namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*}

def afterFaults (G : SimpleGraph V) (F : Finset (Sym2 V)) : SimpleGraph V :=
  G.deleteEdges (F : Set (Sym2 V))

@[simp] theorem mem_afterFaults (G : SimpleGraph V) (F : Finset (Sym2 V)) (e : Sym2 V) :
    e ∈ (afterFaults G F).edgeSet ↔ e ∈ G.edgeSet ∧ e ∉ F := by
  simp [afterFaults, edgeSet_deleteEdges]

theorem afterFaults_mono {G H : SimpleGraph V} (h : G ≤ H) (F : Finset (Sym2 V)) :
    afterFaults G F ≤ afterFaults H F := by
  intro u v huv
  exact ⟨h huv.1, huv.2⟩

/-- Definition 5: finite-stretch fault-tolerant approximation of every actual walk. -/
def IsEFTSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset (Sym2 V), F.card ≤ f →
    IsSpanner (afterFaults G F) (afterFaults H F) w t

/-- Definition 7, including all connected components and all fault sets. -/
def IsFTConnectivityPreserver (G Q : SimpleGraph V) (f : ℕ) : Prop :=
  Q ≤ G ∧ ∀ F : Finset (Sym2 V), F.card ≤ f → ∀ u v,
    (afterFaults G F).Reachable u v ↔ (afterFaults Q F).Reachable u v

def FTCovered (H : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) (f : ℕ)
    (e : Sym2 V) : Prop :=
  ∀ F : Finset (Sym2 V), F.card ≤ f → e ∉ F → Covered (afterFaults H F) w t e

theorem ftCovered_mono {H K : SimpleGraph V} (hHK : H ≤ K)
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {e : Sym2 V}
    (h : FTCovered H w t f e) : FTCovered K w t f e := by
  intro F hF he
  exact covered_mono (afterFaults_mono hHK F) (h F hF he)

theorem ftCovered_of_mem {H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t : ℝ} {f : ℕ} (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e)
    {e : Sym2 V} (he : e ∈ H.edgeSet) : FTCovered H w t f e := by
  intro F _ heF
  exact covered_of_mem ht hw ((mem_afterFaults H F e).mpr ⟨he, heF⟩)

theorem ftCovered_edges_spanner {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t : ℝ} {f : ℕ} (hHG : H ≤ G)
    (h : ∀ e ∈ G.edgeSet, FTCovered H w t f e) : IsEFTSpanner G H w t f := by
  refine ⟨hHG, fun F hF => covered_edges_spanner (afterFaults_mono hHG F) ?_⟩
  intro e he
  obtain ⟨heG,heF⟩ := (mem_afterFaults G F e).mp he
  exact h e heG F hF heF

theorem IsEFTSpanner.connectivity {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t : ℝ} {f : ℕ} (h : IsEFTSpanner G H w t f) : IsFTConnectivityPreserver G H f := by
  refine ⟨h.1, ?_⟩
  intro F hF u v
  constructor
  · rintro ⟨p⟩
    obtain ⟨q,_⟩ := (h.2 F hF).2 u v p
    exact ⟨q⟩
  · exact Reachable.mono (afterFaults_mono h.1 F)

theorem IsEFTSpanner.fault_mono {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t : ℝ} {f g : ℕ} (h : IsEFTSpanner G H w t g) (hfg : f ≤ g) :
    IsEFTSpanner G H w t f := ⟨h.1, fun F hF => h.2 F (hF.trans hfg)⟩

theorem IsFTConnectivityPreserver.fault_mono {G Q : SimpleGraph V}
    {f g : ℕ} (h : IsFTConnectivityPreserver G Q g) (hfg : f ≤ g) :
    IsFTConnectivityPreserver G Q f := ⟨h.1, fun F hF => h.2 F (hF.trans hfg)⟩

/-- Every missing input edge has endpoints connected after every allowed fault
set in the preserver. This is the graph-theoretic fact used for host-tree packing. -/
theorem IsFTConnectivityPreserver.missing_edge_connected {G Q : SimpleGraph V}
    {f : ℕ} (h : IsFTConnectivityPreserver G Q f) {u v : V}
    (heG : G.Adj u v) (heQ : ¬ Q.Adj u v)
    (F : Finset (Sym2 V)) (hF : F.card ≤ f) :
    (afterFaults Q F).Reachable u v := by
  classical
  let F' := F.erase s(u,v)
  have hF' : F'.card ≤ f := card_erase_le.trans hF
  have hconn : (afterFaults G F').Reachable u v :=
    Adj.reachable ⟨heG, by simp [F']⟩
  have heq : afterFaults Q F' = afterFaults Q F := by
    ext a b
    simp only [afterFaults, deleteEdges_adj, mem_coe]
    have hne : Q.Adj a b → s(a,b) ≠ s(u,v) := by
      intro hab he
      exact heQ ((mem_edgeSet Q).mp (he ▸ ((mem_edgeSet Q).mpr hab)))
    simp only [F', mem_erase]
    tauto
  rw [← heq]
  exact (h.2 F' hF' u v).mp hconn

end LightEFTSpanners
