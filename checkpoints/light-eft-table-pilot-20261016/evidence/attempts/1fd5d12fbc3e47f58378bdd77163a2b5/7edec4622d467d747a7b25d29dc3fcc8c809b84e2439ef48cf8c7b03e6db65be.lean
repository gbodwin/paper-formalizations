import LightEFTSpanners.RationalDistanceTable
namespace LightEFTSpanners.RationalDistance.TablePilotComparison
open SimpleGraph
variable {n : ℕ}
def table (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (target : Fin n) : ℕ → Vector (Option ℚ) n :=
  Nat.rec (Vector.ofFn fun u => if u=target then some 0 else none)
    (fun _ prev => step G w prev)
 theorem table_eq_prior (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (target : Fin n) (k : ℕ) :
    table G w target k = LightEFTSpanners.RationalDistance.table G w target k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [table] at ih ⊢
    simp only [LightEFTSpanners.RationalDistance.table]
    rw [ih]
#print axioms table_eq_prior
end LightEFTSpanners.RationalDistance.TablePilotComparison
