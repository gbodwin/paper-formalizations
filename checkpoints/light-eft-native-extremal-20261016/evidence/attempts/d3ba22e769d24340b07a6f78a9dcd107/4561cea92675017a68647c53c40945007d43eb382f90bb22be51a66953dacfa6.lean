import LightSpanners.HikerCompletion
import LightSpanners.ChordWords

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

theorem backwardWalk_getVert (n i : ℕ) (v : V) (hi : i≤n) :
    (C.backwardWalk n v).getVert i=(C.successor.symm : V → V)^[i] v := by
  induction n generalizing v i with
  | zero =>
    have : i=0 := by omega
    subst i
    rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (C.backwardWalk n (C.successor.symm v)).getVert i =
        (C.successor.symm : V → V)^[i+1] v
      rw [ih i _ (by omega),Function.iterate_succ_apply]

variable [Fintype V]

/-- Distinct short backward shifts have distinct actual cycle vertices. -/
theorem backward_iterate_injective (u : V) {s t : ℕ}
    (hs : s<Fintype.card V) (ht : t<Fintype.card V)
    (he : (C.successor.symm : V → V)^[s] u=(C.successor.symm : V → V)^[t] u) : s=t := by
  let m := max s t
  let p := C.backwardWalk m u
  have hm : m<Fintype.card V := max_lt hs ht
  have hp : p.IsPath := C.base_walk_isPath p (C.backwardWalk_nonbacktracking m u)
    (by intro e he
        obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
        rw [← d.edge_symm]
        exact List.mem_map.mpr ⟨d.symm,C.backwardWalk_darts m u d hd,rfl⟩)
    (by simpa [p] using hm)
  apply hp.getVert_injOn
    (by simpa [p,m] using le_max_left s t)
    (by simpa [p,m] using le_max_right s t)
  simpa only [p,C.backwardWalk_getVert m s u (le_max_left _ _),
    C.backwardWalk_getVert m t u (le_max_right _ _)] using he

/-- The first chord bounds the available padding below one full cycle. -/
theorem bucket_padding_lt_card {eps : ℝ} {k i t : ℕ} {e : Sym2 V}
    (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k)))
    (he : e∈G.edgeSet) (hc : e∉C.cycle.edges) (hi : (2:ℝ)^i≤w e)
    (ht : (t:ℝ)≤eps*k*2^i/2) : t<Fintype.card V := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hkr1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hpow : (0:ℝ)<2^i := by positivity
  have hden : 0<2*((1+4*eps)*(2*k)-1) := by nlinarith [mul_pos heps hkr]
  have hweight : w e<(Fintype.card V:ℝ)/(2*((1+4*eps)*(2*k)-1)) := by
    induction e using Sym2.inductionOn with
    | hf u v =>
      exact C.chord_weight_lt hG (by nlinarith [mul_pos heps hkr])
        ((mem_edgeSet G).mp he) hc
  have hm := (lt_div_iff₀ hden).mp hweight
  have hlow := mul_le_mul_of_nonneg_right hi hden.le
  have hcoeff : eps*k/2<2*((1+4*eps)*(2*k)-1) := by nlinarith [mul_pos heps hkr]
  have hsmall := mul_lt_mul_of_pos_right hcoeff hpow
  have hh : (t:ℝ)<Fintype.card V := by nlinarith
  exact_mod_cast hh

end LightSpanners.UnitSpanningCycle
