import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic

namespace LightEFTSpanners
open SimpleGraph

/-- Cutting the closing edge leaves exactly ordinary successive-index edges.
This is the actual graph step behind the lower-construction potential. -/
theorem cycle_delete_closing_le_path (m : ℕ) :
    (cycleGraph (m+3)).deleteEdges {s((0:Fin (m+3)),Fin.last (m+2))} ≤
      pathGraph (m+3) := by
  have forward (u v : Fin (m+3)) (huv : u<v)
      (h : (cycleGraph (m+3)).Adj u v)
      (hne : s(u,v)≠s((0:Fin (m+3)),Fin.last (m+2))) :
      (pathGraph (m+3)).Adj u v := by
    rw [cycleGraph_adj',Fin.coe_sub_iff_lt.mpr huv,
      Fin.coe_sub_iff_le.mpr huv.le] at h
    rcases h with h | h
    · have hu : u=0 := Fin.ext (by simp only [Fin.val_zero]; have := v.isLt; omega)
      have hv : v=Fin.last (m+2) := Fin.ext (by have := u.isLt; have := v.isLt; simp; omega)
      exact (hne (by rw [hu,hv])).elim
    · exact pathGraph_adj.mpr (Or.inl (by omega))
  intro u v h
  obtain ⟨huv,hne⟩ := deleteEdges_adj.mp h
  have hne' : s(u,v)≠s((0:Fin (m+3)),Fin.last (m+2)) := by simpa using hne
  rcases lt_trichotomy u v with hlt | heq | hgt
  · exact forward u v hlt huv hne'
  · exact (huv.ne heq).elim
  · apply Adj.symm
    exact forward v u hgt huv.symm (by simpa only [Sym2.eq_swap] using hne')
end LightEFTSpanners
