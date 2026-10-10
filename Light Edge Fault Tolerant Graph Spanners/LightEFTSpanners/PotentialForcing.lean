import LightEFTSpanners.Basic
import Mathlib.Tactic

namespace LightEFTSpanners
open SimpleGraph LightSpanners
variable {V : Type*}

/-- A real edge potential telescopes along an actual walk. -/
theorem potential_le_walkWeight {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (φ : V → ℝ) (hφ : ∀ u v,G.Adj u v → φ v-φ u≤w s(u,v))
    {u v : V} (p : G.Walk u v) : φ v-φ u≤walkWeight w p := by
  induction p with
  | nil => simp [walkWeight]
  | @cons u v z huv p ih =>
    rw [walkWeight_cons]
    have hs := hφ u v huv
    linarith

/-- A concrete fault set and edge-Lipschitz potential force retention of a
specific original edge. No replacement-distance or spanner conclusion is an
input: the lower bound is derived from the actual returned walk. -/
theorem eft_edge_forced_by_fault_potential {G H : SimpleGraph V}
    {w : Sym2 V → ℝ} {t : ℝ} {f : ℕ} {u v : V}
    (h : IsEFTSpanner G H w t f) (huv : G.Adj u v)
    (F : Finset (Sym2 V)) (hF : F.card≤f) (heF : s(u,v)∉F)
    (φ : V → ℝ)
    (hφ : ∀ a b, ((afterFaults G F).deleteEdges {s(u,v)}).Adj a b →
      φ b-φ a≤w s(a,b)) (hgap : t*w s(u,v)<φ v-φ u) : H.Adj u v := by
  classical
  by_contra hn
  have hnedge : s(u,v)∉H.edgeSet := by simpa only [mem_edgeSet] using hn
  have hsurvive : (afterFaults G F).Adj u v := deleteEdges_adj.mpr ⟨huv,heF⟩
  obtain ⟨p,hp⟩ := (h.2 F hF).2 u v hsurvive.toWalk
  have hpot : φ v-φ u≤walkWeight w p := by
    apply potential_le_walkWeight φ
    intro a b hab
    obtain ⟨habH,habF⟩ := deleteEdges_adj.mp hab
    apply hφ a b
    apply deleteEdges_adj.mpr
    refine ⟨deleteEdges_adj.mpr ⟨h.1 habH,habF⟩,?_⟩
    intro he
    have heq : s(a,b)=s(u,v) := Set.mem_singleton_iff.mp he
    exact hnedge (heq ▸ (mem_edgeSet H).mpr habH)
  have hbound : walkWeight w p≤t*w s(u,v) := by
    simpa [SimpleGraph.Adj.toWalk,walkWeight] using hp
  linarith
end LightEFTSpanners
