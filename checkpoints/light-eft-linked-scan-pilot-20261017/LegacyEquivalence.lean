import LightEFTSpanners.LinkedDistanceKernel
namespace LightEFTSpanners.LinkedDistance.ScanComparison
open RationalDistance
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


theorem scan_eq_prior (r d : List Cell) (z : Cell) :
    scan r d z = LightEFTSpanners.LinkedDistance.scan r d z := by
  induction r generalizing d z with
  | nil => rfl
  | cons a as ih =>
    cases d with
    | nil => rfl
    | cons b bs => exact ih bs (best (addCell a b) z)
#print axioms scan_eq_prior
end LightEFTSpanners.LinkedDistance.ScanComparison
