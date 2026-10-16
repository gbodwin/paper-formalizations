import LightEFTSpanners.LinkedDistanceRefinement

/-! Fixed-fuel execution of the concrete controller. The proof bounds an
actual successful transition trace, rather than a separately assigned work
field. Inputs are a finite list matrix and natural size/endpoint registers;
the semantic contract requires the input matrix to encode the stated graph.
Rational atoms and pointer-cell/register operations define this model. -/
namespace LightEFTSpanners.LinkedDistance
open RationalDistance

 theorem run_terminal (size : ℕ) (M : Matrix) (u v : ℕ) (b : ℚ) (s : State)
    (hs : transition size M u v b s=none) (k : ℕ) : run size M u v b k s=s := by
  cases k <;> simp [run,hs]

 theorem run_add (size : ℕ) (M : Matrix) (u v : ℕ) (b : ℚ) (k m : ℕ) (s : State) :
    run size M u v b (k+m) s=run size M u v b m (run size M u v b k s) := by
  induction k generalizing s with
  | zero => simp [run]
  | succ k ih =>
    cases h : transition size M u v b s with
    | none => simp [run,h,run_terminal size M u v b s h]
    | some t => simpa only [Nat.succ_add,run,h] using ih t

 def bound (n : ℕ) : ℕ := n^3+3*n^2+6*n+4

 def execute (n : ℕ) (M : Matrix) (source target : ℕ) (budget : ℚ) : Bool :=
  match run n M source target budget (bound n) (.init n 0 []) with
  | .halt b => b
  | _ => false

 theorem run_bound_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) :
    run n (matrixOf G w) u.val v.val budget (bound n) (.init n 0 [])=
      .halt (shortTest G w u v budget) := by
  obtain ⟨t,ht,he⟩ := machine_shortTest G w u v budget
  have hh : bound n=t+(bound n-t) := by unfold bound;omega
  rw [hh,run_add,he.run_eq]
  exact run_terminal _ _ _ _ _ _ rfl _

 theorem execute_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) :
    execute n (matrixOf G w) u.val v.val budget=shortTest G w u v budget := by
  simp only [execute,run_bound_eq]

/-- An arbitrary stored matrix may be used; equality is a representation
contract, not an adjacency function consulted by the actual controller. -/
 theorem execute_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (u v : Fin n) (budget : ℚ)
    (M : Matrix) (hM : M=matrixOf G w) :
    (execute n M u.val v.val budget=true ↔
      ∃ p : G.Walk u v,LightSpanners.walkWeight (fun e => (w e:ℝ)) p≤(budget:ℝ)) ∧
    ∃ t,t≤bound n ∧ Executes (transition n M u.val v.val budget) t (.init n 0 [])
      (.halt (execute n M u.val v.val budget)) := by
  subst M
  rw [execute_eq]
  exact ⟨shortTest_iff G w hw u v budget,machine_shortTest G w u v budget⟩

end LightEFTSpanners.LinkedDistance
