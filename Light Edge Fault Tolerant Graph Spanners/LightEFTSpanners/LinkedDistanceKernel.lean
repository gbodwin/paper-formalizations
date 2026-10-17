import LightEFTSpanners.RationalDistanceTest

/-! Concrete linked-list input and distance storage. Every graph entry is an
actual optional rational cell, rather than a supplied adjacency/weight oracle.
The later controller traverses these exact lists. Rational arithmetic remains
an explicit atomic instruction of that machine, not a bit-runtime claim. -/
namespace LightEFTSpanners.LinkedDistance
open RationalDistance
abbrev Cell := Option ℚ
abbrev Matrix := List (List Cell)

def addCell : Cell → Cell → Cell
  | some a, some b => some (a+b)
  | _, _ => none

def scan : List Cell → List Cell → Cell → Cell :=
  fun r => List.rec (motive := fun _ => List Cell → Cell → Cell) (fun _ z => z)
    (fun a _ next d z => match d with
      | [] => z
      | b::bs => next bs (best (addCell a b) z)) r

theorem scan_nil (d : List Cell) (z : Cell) : scan [] d z = z := rfl

theorem scan_cons_nil (a : Cell) (as : List Cell) (z : Cell) :
    scan (a::as) [] z = z := rfl

theorem scan_cons_cons (a b z : Cell) (as bs : List Cell) :
    scan (a::as) (b::bs) z = scan as bs (best (addCell a b) z) := rfl

-- Preserve definitional matching in the unchanged fold and trace proofs.
attribute [reducible] scan

def rows (d : List Cell) : Matrix → List Cell → List Cell :=
  fun rs => List.rec (motive := fun _ => List Cell → List Cell) (fun _ => [])
    (fun r _ next ds => match ds with
      | [] => []
      | a::as => scan r d a :: next as) rs

theorem rows_nil (d ds : List Cell) : rows d [] ds = [] := rfl

theorem rows_cons_nil (d r : List Cell) (rs : Matrix) : rows d (r::rs) [] = [] := rfl

theorem rows_cons_cons (d r : List Cell) (rs : Matrix) (a : Cell) (as : List Cell) :
    rows d (r::rs) (a::as) = scan r d a :: rows d rs as := rfl

-- Preserve definitional matching in the unchanged length and trace proofs.
attribute [reducible] rows

def rounds (M : Matrix) : ℕ → List Cell → List Cell :=
  Nat.rec (motive := fun _ => List Cell → List Cell) (fun d => d)
    (fun _ previous d => previous (rows d M d))

 theorem rounds_zero (M : Matrix) (d : List Cell) : rounds M 0 d = d := rfl

 theorem rounds_succ (M : Matrix) (k : ℕ) (d : List Cell) :
    rounds M (k+1) d = rounds M k (rows d M d) := rfl

 theorem best_assoc (a b c : Cell) : best (best a b) c=best a (best b c) := by
  cases a <;> cases b <;> cases c <;> simp [best,min_assoc]
 theorem best_comm (a b : Cell) : best a b=best b a := by
  cases a <;> cases b <;> simp [best,min_comm]

 theorem scan_best (r d : List Cell) (a b : Cell) :
    scan r d (best a b)=best (scan r d a) b := by
  induction r generalizing d a with
  | nil => rfl
  | cons x xs ih =>
    cases d with
    | nil => rfl
    | cons y ys => simp only [scan,←best_assoc,ih]

 theorem scan_eq_fold (r d : List Cell) (z : Cell) :
    scan r d z=(List.zipWith addCell r d).foldr best z := by
  induction r generalizing d z with
  | nil => rfl
  | cons x xs ih =>
    cases d with
    | nil => rfl
    | cons y ys =>
      change scan xs ys (best (addCell x y) z) =
        best (addCell x y) ((List.zipWith addCell xs ys).foldr best z)
      rw [best_comm (addCell x y) z,scan_best,ih,best_comm]

 theorem rows_length (M : Matrix) (d ds : List Cell) :
    (rows d M ds).length=min M.length ds.length := by
  induction M generalizing ds with
  | nil => simp [rows]
  | cons r rs ih => cases ds <;> simp [rows,ih]

 def matrixOf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℚ) : Matrix :=
  List.ofFn fun u => List.ofFn fun v => if G.Adj u v then some (w s(u,v)) else none

 def initial (n target : ℕ) : List Cell :=
  (List.range n).map fun i => if i=target then some 0 else none

end LightEFTSpanners.LinkedDistance
