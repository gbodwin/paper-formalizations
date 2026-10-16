import LightEFTSpanners.RationalDistanceTest

/-! An explicit unit-cost accounting of the executed relaxation loops.
One charged unit pays each adjacency query, distance or weight-table read, rational addition,
comparison, or loop/write action. Candidate slots are padded to six units,
covering every branch; arbitrary-size rational bit operations are not unit time
in a bit model, and no such bit-runtime conclusion is asserted here. -/
namespace LightEFTSpanners.RationalDistance
open Finset
variable {n : ℕ}

/-- The recursive scan actually computes its result and charges each visited
candidate. It never recursively recomputes the preceding distance table. -/
def scanWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u : Fin n) :
    List (Fin n) → Option ℚ × ℕ
  | [] => (d[u.val],1)
  | v::vs => let r := scanWork G w d u vs
             (best (candidate G w d u v) r.1,r.2+6)

 theorem scanWork_value (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u : Fin n) (l : List (Fin n)) :
    (scanWork G w d u l).1=(l.map (candidate G w d u)).foldr best d[u.val] := by
  induction l with
  | nil => rfl
  | cons v vs ih => simp only [scanWork,List.map_cons,List.foldr_cons,ih]

 theorem scanWork_cost (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) (u : Fin n) (l : List (Fin n)) :
    (scanWork G w d u l).2=1+6*l.length := by
  induction l with
  | nil => rfl
  | cons v vs ih => simp only [scanWork,List.length_cons,ih];omega

/-- Each row is materialized once, and its value and cost are then projected.
The additional n units pay the output-cell writes. -/
def stepWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) : Vector (Option ℚ) n × ℕ :=
  let rows := Vector.ofFn fun u => scanWork G w d u (List.finRange n)
  (rows.map Prod.fst,(∑ u : Fin n,(rows[u.val]).2)+n)

 theorem stepWork_value (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) :
    (stepWork G w d).1=step G w d := by
  apply Vector.ext
  intro i hi
  simp [stepWork,step,scanWork_value]

 theorem stepWork_cost (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (d : Vector (Option ℚ) n) :
    (stepWork G w d).2=n*(6*n+2) := by
  simp [stepWork,scanWork_cost]
  ring

 def tableWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) : ℕ → Vector (Option ℚ) n × ℕ
  | 0 => (table G w v 0,n)
  | k+1 => let prev := tableWork G w v k
           let next := stepWork G w prev.1
           (next.1,prev.2+next.2)

 theorem tableWork_value (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) (k : ℕ) :
    (tableWork G w v k).1=table G w v k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tableWork,stepWork_value,ih,table]

 theorem tableWork_cost (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (v : Fin n) (k : ℕ) :
    (tableWork G w v k).2=n+k*(n*(6*n+2)) := by
  induction k with
  | zero => simp [tableWork]
  | succ k ih => simp only [tableWork,stepWork_cost,ih];ring

 def shortTestWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) : Bool × ℕ :=
  let r := tableWork G w v n
  (test r.1[u.val] budget,r.2+2)

 theorem shortTestWork_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (u v : Fin n) (budget : ℚ) :
    ((shortTestWork G w u v budget).1=true ↔
      ∃ p : G.Walk u v,LightSpanners.walkWeight (fun e => (w e:ℝ)) p≤(budget:ℝ)) ∧
    (shortTestWork G w u v budget).2=6*n^3+2*n^2+n+2 := by
  constructor
  · simpa only [shortTestWork,tableWork_value,shortTest] using shortTest_iff G w hw u v budget
  · simp only [shortTestWork,tableWork_cost];ring

 theorem shortTestWork_value (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) :
    (shortTestWork G w u v budget).1=shortTest G w u v budget := by
  simp only [shortTestWork,tableWork_value,shortTest]

 def coveredWork (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) : Sym2 (Fin n) → Bool × ℕ :=
  Sym2.lift ⟨fun u v => shortTestWork G w u v (t*w s(u,v)),fun u v => by
    change shortTestWork G w u v (t*w s(u,v))=shortTestWork G w v u (t*w s(v,u))
    rw [show s(v,u)=s(u,v) from Sym2.eq_swap]
    apply Prod.ext
    · simp only [shortTestWork_value]
      exact shortTest_symmetric G w hw u v _
    · rw [(shortTestWork_spec G w hw u v _).2,(shortTestWork_spec G w hw v u _).2]⟩

 theorem coveredWork_spec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) (e : Sym2 (Fin n)) :
    (coveredWork G w hw t e).1=coveredTest G w hw t e ∧
    (coveredWork G w hw t e).2=6*n^3+2*n^2+n+2 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [coveredWork,coveredTest,Sym2.lift_mk,shortTestWork_value,true_and]
    exact (shortTestWork_spec G w hw u v _).2
end LightEFTSpanners.RationalDistance
