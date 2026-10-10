import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The exact finite lattice hull used in the higher-dimensional geometric
input. Its vertices are mathlib extreme points, not an assumed direction
family. Translating selected vertices of the integer ball gives bounded
nonnegative average-rigid vectors in every dimension. The sharp number of
vertices is a separate, still unproved theorem. -/
namespace LinearDistancePreservers.LatticeHull
open Finset
attribute [local instance] Classical.propDecidable
variable {D : Type*}

def realVector (z : D → ℤ) : D → ℝ := fun i => (z i : ℝ)

theorem realVector_injective : Function.Injective (realVector (D := D)) := by
  intro z w h
  funext i
  have hi := congrFun h i
  change (z i : ℝ) = (w i : ℝ) at hi
  exact_mod_cast hi

noncomputable def vertices (s : Finset (D → ℤ)) : Finset (D → ℤ) :=
  s.filter (fun z => realVector z ∈ (convexHull ℝ (realVector '' (s : Set (D → ℤ)))).extremePoints ℝ)

/-- The finite filter represents exactly the usual extreme-point set,
not an extra combinatorial surrogate. -/
theorem image_vertices (s : Finset (D → ℤ)) :
    realVector '' (vertices s : Set (D → ℤ)) =
      (convexHull ℝ (realVector '' (s : Set (D → ℤ)))).extremePoints ℝ := by
  ext v
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (mem_filter.mp hz).2
  · intro hv
    obtain ⟨z,hz,rfl⟩ := extremePoints_convexHull_subset hv
    exact ⟨z,mem_filter.mpr ⟨hz,hv⟩,rfl⟩

/-- Averaging lattice vertices to one of those vertices is constant. -/
theorem average_unique {s : Finset (D → ℤ)} {m : ℕ}
    (a : D → ℤ) (ha : a ∈ vertices s) (f : Fin m → D → ℤ)
    (hf : ∀ j, f j ∈ vertices s)
    (hsum : ∀ d, ∑ j, f j d = (m : ℤ)*a d) : ∀ j, f j = a := by
  classical
  let P := convexHull ℝ (realVector '' (s : Set (D → ℤ)))
  have hext : realVector a ∈ P.extremePoints ℝ := (mem_filter.mp ha).2
  have hconv : Convex ℝ (P \ {realVector a}) :=
    ((convex_convexHull ℝ _).mem_extremePoints_iff_convex_sdiff.mp hext).2
  intro i
  by_contra hne
  let B : Finset (Fin m) := univ.filter fun j => f j ≠ a
  have hi : i ∈ B := mem_filter.mpr ⟨mem_univ _,hne⟩
  have hB : 0 < B.card := card_pos.mpr ⟨i,hi⟩
  have hBr : (B.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hsumB (d : D) : ∑ j ∈ B, realVector (f j) d = (B.card : ℝ)*realVector a d := by
    have hall : ∑ j : Fin m, ((f j d : ℝ)-(a d : ℝ)) = 0 := by
      rw [sum_sub_distrib]
      have hh : ∑ j : Fin m, (f j d : ℝ) = (m : ℝ)*(a d : ℝ) := by exact_mod_cast hsum d
      simp [hh]
    have hremove : ∑ j ∈ B, ((f j d : ℝ)-(a d : ℝ)) =
        ∑ j : Fin m, ((f j d : ℝ)-(a d : ℝ)) := by
      apply sum_subset (subset_univ B)
      intro j _ hj
      have hj' : f j = a := by simpa [B] using hj
      rw [hj',sub_self]
    rw [← hremove,sum_sub_distrib] at hall
    simp only [sum_const,nsmul_eq_mul] at hall
    change ∑ j ∈ B, (f j d : ℝ) = (B.card : ℝ)*(a d : ℝ)
    linarith
  have hmem : (∑ j ∈ B, (B.card : ℝ)⁻¹ • realVector (f j)) ∈ P \ {realVector a} := by
    apply hconv.sum_mem (fun _ _ => inv_nonneg.mpr (by positivity)) (by simp [hBr])
    intro j hj
    refine ⟨subset_convexHull ℝ _ ⟨f j,(mem_filter.mp (hf j)).1,rfl⟩,?_⟩
    intro h
    exact (mem_filter.mp hj).2 (realVector_injective (Set.mem_singleton_iff.mp h))
  have heq : (∑ j ∈ B, (B.card : ℝ)⁻¹ • realVector (f j)) = realVector a := by
    funext d
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,← mul_sum,hsumB]
    rw [← mul_assoc,inv_mul_cancel₀ hBr,one_mul]
  exact hmem.2 (by rw [heq]; rfl)

noncomputable def ball (d R : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset (fun _ : Fin d => Icc (-(R : ℤ)) R)).filter
    (fun z => ∑ i, (z i)^2 ≤ (R : ℤ)^2)

/-- The bounded finite implementation contains exactly the lattice points
in the closed Euclidean ball, stated through squared coordinates. -/
theorem mem_ball {d R : ℕ} {z : Fin d → ℤ} :
    z ∈ ball d R ↔ ∑ i, (z i)^2 ≤ (R : ℤ)^2 := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_,h⟩
    intro i
    have hi : (z i)^2 ≤ ∑ j, (z j)^2 := single_le_sum (fun j _ => sq_nonneg (z j)) (mem_univ i)
    have hR : (0 : ℤ) ≤ R := Int.natCast_nonneg _
    apply mem_Icc.mpr
    constructor <;> nlinarith

theorem ball_bounds {d R : ℕ} {z : Fin d → ℤ} (hz : z ∈ ball d R) (i : Fin d) :
    -(R : ℤ) ≤ z i ∧ z i ≤ R :=
  mem_Icc.mp (Fintype.mem_piFinset.mp (mem_filter.mp hz).1 i)

/-- Any prescribed number of lattice-ball vertices can be translated
into distinct nonnegative integer directions. The only hypothesis is
cardinality; rigidity and the coordinate bound are proved. -/
theorem exists_directions {d R x : ℕ} (hx : x ≤ (vertices (ball d R)).card) :
    ∃ v : Fin x → Fin d → ℕ,
      Function.Injective v ∧ (∀ a i, v a i < 2*R+1) ∧
        ∀ (m : ℕ) (a : Fin x) (g : Fin m → Fin x),
          (∀ i, ∑ j, (v (g j) i : ℤ) = (m : ℤ)*(v a i : ℤ)) →
            ∀ j, v (g j) = v a := by
  classical
  have hcard : Fintype.card (Fin x) ≤ Fintype.card (vertices (ball d R)) := by
    simpa using hx
  let f : Fin x ↪ vertices (ball d R) :=
    (Function.Embedding.nonempty_of_card_le hcard).some
  let w : Fin x → Fin d → ℤ := fun a => (f a).val
  have hw (a) : w a ∈ vertices (ball d R) := (f a).property
  have hb (a) (i) : -(R : ℤ) ≤ w a i ∧ w a i ≤ R :=
    ball_bounds (mem_filter.mp (hw a)).1 i
  let v : Fin x → Fin d → ℕ := fun a i => (w a i + R).toNat
  have hvcast (a) (i) : (v a i : ℤ) = w a i + R :=
    Int.toNat_of_nonneg (by have := (hb a i).1; omega)
  have hwinj : Function.Injective w := Subtype.val_injective.comp f.injective
  refine ⟨v,?_,?_,?_⟩
  · intro a b hab
    apply hwinj
    funext i
    have hi : (v a i : ℤ) = (v b i : ℤ) := by rw [congrFun hab i]
    rw [hvcast,hvcast] at hi
    omega
  · intro a i
    have hi := (hb a i).2
    have hc := hvcast a i
    omega
  · intro m a g hsum j
    have hsum' (i) : ∑ j, w (g j) i = (m : ℤ)*w a i := by
      have hi := hsum i
      simp only [hvcast,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
      nlinarith
    have heq := average_unique (w a) (hw a) (w ∘ g) (fun j => hw (g j)) hsum' j
    funext i
    change (w (g j) i + R).toNat = (w a i + R).toNat
    change w (g j) = w a at heq
    rw [heq]

end LinearDistancePreservers.LatticeHull
