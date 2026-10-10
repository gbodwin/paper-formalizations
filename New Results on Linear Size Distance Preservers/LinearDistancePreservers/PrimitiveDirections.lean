import LinearDistancePreservers.ConvexChains
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-! Primitive lattice slopes and sharp planar convex chains.
The counting argument discards pairs sharing any divisor at least two.
A telescoping bound on the reciprocal-square sum leaves at least one
quarter of the square. No asymptotic or coprimality-density theorem is assumed. -/
namespace LinearDistancePreservers.PrimitiveDirections
open Finset
attribute [local instance] Classical.propDecidable

def box (R : ℕ) : Finset (ℕ × ℕ) := Ioc 0 R ×ˢ Ioc 0 R

def primitive (R : ℕ) : Finset (ℕ × ℕ) :=
  (box R).filter (fun p => p.1.Coprime p.2)

noncomputable def slope (p : ℕ × ℕ) : ℝ := (p.2 : ℝ) / p.1

/-- An elementary uniform bound, retaining a telescoping remainder. -/
theorem reciprocal_square_sum (n : ℕ) :
    (∑ i ∈ range n, (1 : ℝ) / ((i : ℝ)+2)^2) ≤
      3/4 - 3/(2*((n : ℝ)+2)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_add, Nat.cast_one]
    have hstep : (1 : ℝ)/((n : ℝ)+2)^2 ≤
        3/(2*((n : ℝ)+2)) - 3/(2*((n : ℝ)+3)) := by
      have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ)+2)^2)).mpr
      field_simp
      nlinarith
    have he : (n : ℝ)+1+2 = (n : ℝ)+3 := by ring
    rw [he]
    linarith

/-- Common-divisor pairs account for at most three quarters of the box. -/
theorem divided_square_sum (R : ℕ) :
    (∑ i ∈ range R, ((R / (i+2) : ℕ) : ℝ)^2) ≤ 3/4*(R : ℝ)^2 := by
  calc
    _ ≤ ∑ i ∈ range R, ((R : ℝ)/((i : ℝ)+2))^2 := by
      apply sum_le_sum
      intro i _
      have h : ((R/(i+2) : ℕ) : ℝ) ≤ (R : ℝ)/(i+2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (Nat.cast_div_le (m := R) (n := i+2) (α := ℝ))
      exact pow_le_pow_left₀ (by positivity) h 2
    _ = (R : ℝ)^2 * ∑ i ∈ range R, (1 : ℝ)/((i : ℝ)+2)^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [div_pow]
      ring
    _ ≤ (R : ℝ)^2 * (3/4 - 3/(2*((R : ℝ)+2))) :=
      mul_le_mul_of_nonneg_left (reciprocal_square_sum R) (sq_nonneg _)
    _ ≤ 3/4*(R : ℝ)^2 := by
      have : 0 ≤ (R : ℝ)^2 * (3/(2*((R : ℝ)+2))) := by positivity
      nlinarith

/-- At least one quarter of positive pairs in the square are primitive. -/
theorem primitive_card_lower (R : ℕ) : R^2 ≤ 4*(primitive R).card := by
  let bad := (box R).filter (fun p => ¬p.1.Coprime p.2)
  let multiples := fun d : ℕ => (Ioc 0 R).filter (fun a => d ∣ a)
  have hcover : bad ⊆ (range R).biUnion
      (fun i => multiples (i+2) ×ˢ multiples (i+2)) := by
    intro p hp
    have hp' := mem_filter.mp hp
    have hb := mem_product.mp hp'.1
    have ha := mem_Ioc.mp hb.1
    have hc := mem_Ioc.mp hb.2
    let d := p.1.gcd p.2
    have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha.1
    have hd1 : d ≠ 1 := hp'.2
    have hd2 : 2 ≤ d := by omega
    have hdR : d ≤ R := (Nat.le_of_dvd ha.1 (Nat.gcd_dvd_left _ _)).trans ha.2
    apply mem_biUnion.mpr
    refine ⟨d-2, mem_range.mpr (by omega), ?_⟩
    have hd : d-2+2 = d := by omega
    simp only [hd, mem_product, multiples, mem_filter]
    exact ⟨⟨hb.1, Nat.gcd_dvd_left _ _⟩, ⟨hb.2, Nat.gcd_dvd_right _ _⟩⟩
  have hbad : bad.card ≤ ∑ i ∈ range R, (R/(i+2))^2 := by
    calc
      _ ≤ ((range R).biUnion (fun i => multiples (i+2) ×ˢ multiples (i+2))).card :=
        card_le_card hcover
      _ ≤ ∑ i ∈ range R, (multiples (i+2) ×ˢ multiples (i+2)).card := card_biUnion_le
      _ = _ := by simp [multiples, card_product, Nat.Ioc_filter_dvd_card_eq_div, pow_two]
  have htotal : (primitive R).card + bad.card = R^2 := by
    simpa [primitive, bad, box, card_product, pow_two] using
      (card_filter_add_card_filter_not (s := box R) (p := fun p => p.1.Coprime p.2))
  have hbad' : (bad.card : ℝ) ≤ 3/4*(R : ℝ)^2 := by
    have hh : (bad.card : ℝ) ≤ ∑ i ∈ range R, ((R/(i+2) : ℕ) : ℝ)^2 := by
      exact_mod_cast hbad
    exact hh.trans (divided_square_sum R)
  have htotal' : ((primitive R).card : ℝ) + bad.card = (R : ℝ)^2 := by
    exact_mod_cast htotal
  have hh : (R : ℝ)^2 ≤ 4*((primitive R).card : ℝ) := by linarith
  exact_mod_cast hh

theorem primitive_card_upper (R : ℕ) : (primitive R).card ≤ R^2 := by
  simpa [primitive, box, card_product, pow_two] using card_le_card (filter_subset
    (fun p : ℕ × ℕ => p.1.Coprime p.2) (box R))

/-- Different primitive pairs have different slopes. -/
theorem slope_injective {R : ℕ} : Set.InjOn slope (primitive R) := by
  intro p hp q hq h
  have hp' := mem_filter.mp hp
  have hq' := mem_filter.mp hq
  have hp0 : 0 < p.1 := (mem_Ioc.mp (mem_product.mp hp'.1).1).1
  have hq0 : 0 < q.1 := (mem_Ioc.mp (mem_product.mp hq'.1).1).1
  have he : p.2*q.1 = q.2*p.1 := by
    have hh := (div_eq_div_iff (by exact_mod_cast hp0.ne')
      (by exact_mod_cast hq0.ne')).mp h
    exact_mod_cast hh
  have hfirst : p.1 = q.1 := by
    calc
      p.1 = Nat.gcd (q.1*p.1) (q.2*p.1) := by rw [Nat.gcd_mul_right, hq'.2, one_mul]
      _ = Nat.gcd (p.1*q.1) (p.2*q.1) := by rw [mul_comm q.1 p.1, he]
      _ = q.1 := by rw [Nat.gcd_mul_right, hp'.2, one_mul]
  apply Prod.ext hfirst
  rw [hfirst] at he
  exact Nat.eq_of_mul_eq_mul_right hq0 he

/-- Sort all primitive slopes, then take the exposed vertices of their
integer chain. This is an actual growing direction family, with no
slope, cardinality, or geometric assumptions supplied by the caller. -/
theorem exists_planar_directions (R : ℕ) :
    ∃ m : ℕ, R^2 ≤ 4*m ∧ m ≤ R^2 ∧
      ∃ v : Fin (m+1) → Bool → ℕ,
        Function.Injective v ∧ (∀ t q, v t q < R^3+1) ∧
          DirectionGraph.AverageRigid v := by
  classical
  let s := (primitive R).image slope
  have hcard : s.card = (primitive R).card := card_image_of_injOn slope_injective
  let e := s.orderEmbOfFin hcard
  have hpre : ∀ i : Fin (primitive R).card,
      ∃ p ∈ primitive R, slope p = e i := by
    intro i
    exact mem_image.mp (s.orderEmbOfFin_mem hcard i)
  choose p hp hs using hpre
  let a := fun i => (p i).1
  let b := fun i => (p i).2
  have ha (i) : 0 < a i ∧ a i ≤ R :=
    mem_Ioc.mp (mem_product.mp (mem_filter.mp (hp i)).1).1
  have hb (i) : b i ≤ R :=
    (mem_Ioc.mp (mem_product.mp (mem_filter.mp (hp i)).1).2).2
  have hmono : StrictMono (fun i => (b i : ℝ)/(a i : ℝ)) := by
    intro i j hij
    change slope (p i) < slope (p j)
    rw [hs i, hs j]
    exact e.strictMono hij
  obtain ⟨v,hi,hv,hr⟩ := ConvexChains.exists_directions a b
    (fun i => (ha i).1) (fun i => (ha i).2) hb hmono
  refine ⟨(primitive R).card, primitive_card_lower R, primitive_card_upper R, v,hi,?_,hr⟩
  intro t q
  have hmul := Nat.mul_le_mul_right R (primitive_card_upper R)
  have hpow : R^2*R = R^3 := by ring
  rw [hpow] at hmul
  exact (hv t q).trans_le (Nat.add_le_add_right hmul 1)

/-- A prescribed number of planar directions, under only a numerical
capacity inequality. -/
theorem exists_planar_directions_of_card {R x : ℕ} (hx : 4*x ≤ R^2) :
    ∃ v : Fin x → Bool → ℕ,
      Function.Injective v ∧ (∀ t q, v t q < R^3+1) ∧
        DirectionGraph.AverageRigid v := by
  obtain ⟨m,hm,_,v,hi,hv,hr⟩ := exists_planar_directions R
  have hxm : x ≤ m+1 := by omega
  let f : Fin x → Fin (m+1) := Fin.castLE hxm
  refine ⟨v ∘ f, hi.comp (Fin.castLE_injective hxm), ?_, ?_⟩
  · intro t q
    exact hv (f t) q
  · intro n a g hsum i
    exact hr n (f a) (f ∘ g) hsum i

/-- Sharp planar growth at every side length, in an integer-power form.
The constant is deliberately coarse; r need not be a cube. -/
theorem exists_planar_directions_in_box {r : ℕ} (hr : 2 ≤ r) :
    ∃ x : ℕ, (r-1)^2 ≤ 4096*x^3 ∧
      ∃ v : Fin x → Bool → ℕ,
        Function.Injective v ∧ (∀ t q, v t q < r) ∧
          DirectionGraph.AverageRigid v := by
  let B := Nat.nthRoot 3 (r-1)
  have hlo : B^3 ≤ r-1 := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hhi : r-1 < (B+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hB : 1 ≤ B := by
    by_contra h
    have : B = 0 := by omega
    simp [this] at hhi
    omega
  have h8 : r-1 ≤ 8*B^3 := by
    have hp := Nat.pow_le_pow_left (show B+1 ≤ 2*B by omega) 3
    nlinarith
  obtain ⟨m,hm,_,v,hinj,hv,hc⟩ := exists_planar_directions B
  refine ⟨m+1, ?_, v, hinj, ?_, hc⟩
  · calc
      (r-1)^2 ≤ (8*B^3)^2 := Nat.pow_le_pow_left h8 2
      _ = 64*(B^2)^3 := by ring
      _ ≤ 64*(4*m)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 3)
      _ = 4096*m^3 := by ring
      _ ≤ 4096*(m+1)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  · intro t q
    exact (hv t q).trans_le (by omega)

end LinearDistancePreservers.PrimitiveDirections
