import LinearDistancePreservers.ExactLayerDirections
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Tactic

namespace LinearDistancePreservers.DirectionEncoding

/-- Integer rounding in the exact arbitrary-layer-cardinality regime. This
power form is equivalent to the source's fixed-dimension density exponent. -/
theorem rounded_direction_scale {d x C k N : ℕ} (hd : 2≤d) (hx : 0<x)
    (hbudget : ((k+1)*C*2^(d+1))^(d*(d-1))*x^(d+1)≤N^(d-1)) :
    ∃ b : ℕ, 0<b ∧ x≤b^(d*(d-1)) ∧ ((k+1)*C*b^(d+1))^d≤N := by
  let e := d*(d-1)
  have he : e≠0 := Nat.mul_ne_zero (by omega) (by omega)
  let u := Nat.nthRoot e x
  have hu : u^e≤x := Nat.pow_nthRoot_le (Or.inl he)
  have hu' : x<(u+1)^e := Nat.lt_pow_nthRoot_add_one he x
  have hu0 : 0<u := by
    by_contra h
    have hz : u=0 := by omega
    simp only [hz,zero_add,one_pow] at hu'
    omega
  let b := u+1
  have hb : b≤2*u := by dsimp [b]; omega
  have hbE : b^(e*(d+1))≤2^(e*(d+1))*x^(d+1) := by
    calc
      _ ≤ (2*u)^(e*(d+1)) := Nat.pow_le_pow_left hb _
      _ = 2^(e*(d+1))*(u^e)^(d+1) := by rw [mul_pow,← pow_mul]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu _)
  refine ⟨b,by dsimp [b]; omega,hu'.le,?_⟩
  apply (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (show d-1≠0 by omega)).mp
  calc
    (((k+1)*C*b^(d+1))^d)^(d-1)
      = ((k+1)*C)^e*b^(e*(d+1)) := by
        simp only [mul_pow,← pow_mul]
        dsimp [e]
        congr 1
        congr 1
        ring
    _ ≤ ((k+1)*C)^e*(2^(e*(d+1))*x^(d+1)) := Nat.mul_le_mul_left _ hbE
    _ = ((k+1)*C*2^(d+1))^e*x^(d+1) := by
      simp only [mul_pow,← pow_mul]
      rw [Nat.mul_comm e (d+1)]
      ring
    _ ≤ N^(d-1) := hbudget

end LinearDistancePreservers.DirectionEncoding

namespace LinearDistancePreservers.DirectionEncoding
open SimpleGraph Finset DirectionGraph
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- A finite, fully quantified version of the auxiliary unweighted perfect
path construction, with arbitrary exact prescribed layer cardinality.
The radius constant is fixed only by d, before every graph parameter. -/
theorem exact_arbitrary_layer_size (d : ℕ) (hd : 2≤d) :
    ∃ K : ℕ, 0<K ∧ ∀ N k x : ℕ, ∀ [NeZero N], 0<k →
      ((k+1)*K)^(d*(d-1))*x^(d+1)≤N^(d-1) →
    ∃ w : Fin x → Unit → ℕ,
      Fintype.card (Unit → ZMod N)=N ∧
      (graph w N k).edgeFinset.card=k*N*x ∧
      Function.Injective (fun p : (Unit → ZMod N) × Fin x =>
        (canonicalWalk (k := k) w p.1 p.2).support) ∧
      (∀ u : Vertex Unit N k,
        Fintype.card {p : (Unit → ZMod N) × Fin x // u∈(canonicalWalk w p.1 p.2).support}=x) ∧
      (∀ e : Sym2 (Vertex Unit N k), e∈(graph w N k).edgeSet →
        ∃! p : (Unit → ZMod N) × Fin x, e∈(canonicalWalk w p.1 p.2).edges) ∧
      (∀ (s : Unit → ZMod N) (a : Fin x)
        (q : (graph w N k).Walk (point w s a 0) (point w s a (Fin.last k))),
        q.length≤k → q=canonicalWalk w s a) := by
  obtain ⟨C,hC,hdirs⟩ := uniform_bounded_directions d hd
  refine ⟨C*2^(d+1),by positivity,?_⟩
  intro N k x hN hk hbudget
  letI : NeZero N := hN
  by_cases hx0 : x=0
  · subst x; exact zero_layer_family
  have hx : 0<x := by omega
  have hbudget' : ((k+1)*C*2^(d+1))^(d*(d-1))*x^(d+1)≤N^(d-1) := by
    simpa only [mul_assoc] using hbudget
  obtain ⟨b,hb,hxb,hsize⟩ := rounded_direction_scale hd hx hbudget'
  obtain ⟨v,hi,hv,hr⟩ := hdirs b x hb hxb
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, d=m+1 := ⟨d-1,by omega⟩
  apply exact_layer_perfect (r := C*b^(m+1+1)) (by positivity) hk v hi hv hr
  simpa only [mul_assoc] using hsize

end LinearDistancePreservers.DirectionEncoding
