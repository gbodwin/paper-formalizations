import LightEFTSpanners.RationalDistanceTable

namespace LightEFTSpanners.RationalDistance
open SimpleGraph LightSpanners
variable {n : ℕ}

 theorem cast_cost (w : Sym2 (Fin n) → ℚ) {G : SimpleGraph (Fin n)} {u v : Fin n}
    (p : G.Walk u v) : (cost w p : ℝ)=walkWeight (fun e => (w e:ℝ)) p := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih]

/-- Executable shortest-walk threshold test using n finite relaxation rounds.
No path enumeration, minimum-path choice or real comparison is executed. -/
def shortTest (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) : Bool :=
  test (table G w v n)[u.val] budget

 theorem shortTest_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (u v : Fin n) (budget : ℚ) :
    shortTest G w u v budget=true ↔
      ∃ p : G.Walk u v,walkWeight (fun e => (w e:ℝ)) p≤(budget:ℝ) := by
  rw [shortTest,test_eq_true,below_table_iff]
  constructor
  · rintro ⟨p,_,hp⟩
    exact ⟨p,by rw [←cast_cost];exact_mod_cast hp⟩
  · rintro ⟨p,hp⟩
    refine ⟨p.bypass,?_,?_⟩
    · have h := p.bypass_isPath.length_lt
      simpa only [Fintype.card_fin] using h.le
    · have h := (walkWeight_bypass_le (fun e => (w e:ℝ))
        (fun e => by exact_mod_cast hw e) p).trans hp
      rw [←cast_cost] at h
      exact_mod_cast h

 theorem shortTest_symmetric (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (u v : Fin n) (budget : ℚ) :
    shortTest G w u v budget=shortTest G w v u budget := by
  apply Bool.eq_iff_iff.mpr
  simp only [shortTest_iff G w hw]
  constructor <;> rintro ⟨p,hp⟩ <;> refine ⟨p.reverse,?_⟩ <;>
    simpa [walkWeight] using hp

/-- Quotient lifting chooses neither an arbitrary representative nor a path.
Swapping an edge's endpoints leaves the executable Boolean unchanged. -/
def coveredTest (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) : Sym2 (Fin n) → Bool :=
  Sym2.lift ⟨fun u v => shortTest G w u v (t*w s(u,v)),fun u v => by
    change shortTest G w u v (t*w s(u,v))=shortTest G w v u (t*w s(v,u))
    rw [show s(v,u)=s(u,v) from Sym2.eq_swap]
    exact shortTest_symmetric G w hw u v _⟩

 theorem coveredTest_iff (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) :
    coveredTest G w hw t e=true ↔ Covered G (fun d => (w d:ℝ)) (t:ℝ) e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [coveredTest,Sym2.lift_mk,shortTest_iff G w hw,Rat.cast_mul]
    constructor
    · intro h a b hab
      rcases Sym2.eq_iff.mp hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h
      · obtain ⟨p,hp⟩ := h
        exact ⟨p.reverse,by simpa [walkWeight,Sym2.eq_swap] using hp⟩
    · exact fun h => h u v rfl
end LightEFTSpanners.RationalDistance
