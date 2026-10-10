import LightEFTSpanners.CycleLinearization
import Mathlib.Combinatorics.SimpleGraph.Circulant

namespace LightEFTSpanners
open SimpleGraph

/-- Translate the cut to the closing edge; the potential then increases by two
per ordinary cycle step. This supplies the actual base potential, not a lower
bound assumption about shortest paths. -/
def cyclePotential (m : ℕ) (r a : Fin (m+3)) : ℝ := 2*((a-r).val:ℝ)

theorem cyclePotential_gap (m : ℕ) (r : Fin (m+3)) :
    cyclePotential m r (r-1)-cyclePotential m r r=2*(m+2) := by
  have he : (r-1)-r=(-1:Fin (m+3)) := by abel
  simp [cyclePotential,he]

theorem cyclePotential_lipschitz (m : ℕ) (r a b : Fin (m+3))
    (hab : ((cycleGraph (m+3)).deleteEdges {s(r,r-1)}).Adj a b) :
    |cyclePotential m r b-cyclePotential m r a|≤2 := by
  obtain ⟨hab,hne⟩ := deleteEdges_adj.mp hab
  have htrans : (cycleGraph (m+3)).Adj (a-r) (b-r) := by
    rw [cycleGraph_adj] at hab ⊢
    have h1 : (a-r)-(b-r)=a-b := by abel
    have h2 : (b-r)-(a-r)=b-a := by abel
    simpa only [h1,h2] using hab
  have hlast : (Fin.last (m+2):Fin (m+3))=-1 := Fin.ext (by simp)
  have hzero {z : Fin (m+3)} (hz : z-r=0) : z=r := sub_eq_zero.mp hz
  have hend {z : Fin (m+3)} (hz : z-r=Fin.last (m+2)) : z=r-1 := by
    rw [hlast] at hz
    have he := (sub_eq_iff_eq_add).mp hz
    calc z = -1+r := he
         _ = r-1 := by abel
  have hcut : ((cycleGraph (m+3)).deleteEdges {s((0:Fin (m+3)),Fin.last (m+2))}).Adj
      (a-r) (b-r) := by
    refine deleteEdges_adj.mpr ⟨htrans,?_⟩
    intro he
    have heq := Sym2.eq_iff.mp (Set.mem_singleton_iff.mp he)
    apply hne
    apply Set.mem_singleton_iff.mpr
    rcases heq with h | h
    · rw [hzero h.1,hend h.2]
    · rw [hend h.1,hzero h.2,Sym2.eq_swap]
  have hp := pathGraph_adj.mp (cycle_delete_closing_le_path m hcut)
  simp only [cyclePotential]
  rw [abs_le]
  rcases hp with hp | hp
  · have hr : ((a-r).val:ℝ)+1=((b-r).val:ℝ) := by exact_mod_cast hp
    constructor <;> linarith
  · have hr : ((b-r).val:ℝ)+1=((a-r).val:ℝ) := by exact_mod_cast hp
    constructor <;> linarith
end LightEFTSpanners
