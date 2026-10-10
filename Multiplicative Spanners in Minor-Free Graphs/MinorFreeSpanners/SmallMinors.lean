import MinorFreeSpanners.Minor
import Mathlib.Tactic.FinCases

/-! The paper's lower-bound proof needs h≥3 in its bounded-h tree case.
K₂-minor-free graphs are edgeless, so a positive linear lower bound cannot
hold there. This is a graph-level domain clarification. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*}

def edgeEmbedding {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) : Fin 2 ↪ V where
  toFun := fun i => if i = 0 then u else v
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [huv.ne,huv.ne.symm]

def edgeMinorModel {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    MinorModel (⊤ : SimpleGraph (Fin 2)) G :=
  MinorModel.ofEmbedding _ _ (edgeEmbedding huv) (by
    intro i j hij
    change G.Adj (if i = 0 then u else v) (if j = 0 then u else v)
    fin_cases i <;> fin_cases j <;> simp_all [huv.symm])

theorem cliqueMinorFree_two_iff (G : SimpleGraph V) : CliqueMinorFree G 2 ↔ G = ⊥ := by
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro u v huv
    exact (h ⟨edgeMinorModel huv⟩).elim
  · rintro rfl ⟨M⟩
    obtain ⟨u, hu, v, hv, huv⟩ := M.adjacent 0 1 (by decide)
    exact huv

end MinorFreeSpanners
