import LightEFTSpanners.RationalDistanceWork
namespace LightEFTSpanners.RationalDistance.DistanceWorkPilotComparison
open Finset
variable {n : ℕ}
def scanWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u : Fin n) :
    List (Fin n) → Option ℚ × ℕ :=
  List.rec (d[u.val],1) (fun v _ r =>
    (best (candidate G w d u v) r.1,r.2+6))
 theorem scanWork_eq_prior (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u : Fin n) (l : List (Fin n)) :
    scanWork G w d u l = LightEFTSpanners.RationalDistance.scanWork G w d u l := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    simp only [scanWork] at ih ⊢
    simp only [LightEFTSpanners.RationalDistance.scanWork]
    rw [ih]
#print axioms scanWork_eq_prior
def stepWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) : Vector (Option ℚ) n × ℕ :=
  let rows := Vector.ofFn fun u => scanWork G w d u (List.finRange n)
  (rows.map Prod.fst,(∑ u : Fin n,(rows[u.val]).2)+n)
 theorem stepWork_eq_prior (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) :
    stepWork G w d = LightEFTSpanners.RationalDistance.stepWork G w d := by
  simp only [stepWork,scanWork_eq_prior,LightEFTSpanners.RationalDistance.stepWork]
#print axioms stepWork_eq_prior
def tableWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) : ℕ → Vector (Option ℚ) n × ℕ :=
  Nat.rec (table G w v 0,n) (fun _ prev =>
    let next := stepWork G w prev.1
    (next.1,prev.2+next.2))
 theorem tableWork_eq_prior (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) (k : ℕ) :
    tableWork G w v k = LightEFTSpanners.RationalDistance.tableWork G w v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [tableWork] at ih ⊢
    simp only [LightEFTSpanners.RationalDistance.tableWork]
    rw [ih]
    simp only [stepWork_eq_prior]
#print axioms tableWork_eq_prior
end LightEFTSpanners.RationalDistance.DistanceWorkPilotComparison
