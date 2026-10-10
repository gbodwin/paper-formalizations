import GreedyShortcuts.PathFourPackedOutput
import GreedyShortcuts.ChainMomentSharp

/-! The moment bound for the already constructed four-hop/packed-cover output.
An internal ninth-root scale gives the sharper weaker finite DAG theorem;
universal maximum-distance cubic progress and near-linear size remain open. -/
namespace GreedyShortcuts.UniformChainPacking
open Finset DirectedPaths ChainUnion ChainCover
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fourHopPackedOutput_moment_card (G : V → V → Prop)
    (hG : CanonicalSegments.Acyclic G) (r R : ℕ) (hr : 3≤r) (hR : 0<R)
    (hn : Fintype.card V≤r^3) (hscale : R^3≤r^2) :
    (fourHopPackedOutput G hG r hr).card ≤
      (6*PathFour.height r+1)*Fintype.card V+2*(256*(Fintype.card V*r^2)/R^2+1) := by
  classical
  let T := context G hG r (6*PathFour.height r+1) (PathFour.ambientWitness r r (Nat.le_refl _))
  have hI : Fintype.card {c // c∈packing G r} ≤ r^2 := by
    have hpack := packing_card_mul G r
    have hm : (packing G r).card*r≤r^2*r := by nlinarith
    have hc := Nat.le_of_mul_le_mul_right hm (by omega : 0<r)
    simpa only [Fintype.card_coe] using hc
  have hnum := Nat.mul_le_mul_left 256 (Nat.mul_le_mul_left (Fintype.card V) hI)
  have hdiv := Nat.div_le_div_right (c := R^2) hnum
  have hc := T.shortcuts_card_moment_sharp r R hr hR hscale
  change (fourHopPackedOutput G hG r hr).card ≤ (6*PathFour.height r+1)*Fintype.card V+
    2*(256*(Fintype.card V*Fintype.card {c // c∈packing G r})/R^2+1) at hc
  omega

/-- An exact integer parameterization of the n^(11/9)-scale weaker bound. -/
theorem fourHopPackedOutput_ninth_scale (G : V → V → Prop)
    (hG : CanonicalSegments.Acyclic G) (k : ℕ) (hk : 2≤k)
    (hn : Fintype.card V≤k^9) :
    let hr : 3≤k^3 := (by have h := Nat.pow_le_pow_left hk 3;norm_num at h;omega)
    fourHopPackedOutput G hG (k^3) hr ⊆ candidates G ∧
    (fourHopPackedOutput G hG (k^3) hr).card ≤
      (6*PathFour.height (k^3)+1)*Fintype.card V+512*Fintype.card V*k^2+2 ∧
    ∀ s t,Reachable G s t → ∃ q : DWalk s t,
      Allowed (augment G (fourHopPackedOutput G hG (k^3) hr)) q ∧ q.length≤7*k^3+2 := by
  dsimp only []
  have hr : 3≤k^3 := by have h := Nat.pow_le_pow_left hk 3;norm_num at h;omega
  have hn' : Fintype.card V≤(k^3)^3 := by simpa only [← pow_mul] using hn
  have hs := fourHopPackedOutput_spec G hG (k^3) hr hn'
  refine ⟨hs.1,?_,hs.2.2⟩
  have hc := fourHopPackedOutput_moment_card G hG (k^3) (k^2) hr
    (pow_pos (by omega : 0<k) 2) hn' (by simp only [← pow_mul];norm_num)
  have he : 256*(Fintype.card V*(k^3)^2) = (256*Fintype.card V*k^2)*(k^2)^2 := by ring
  rw [he,Nat.mul_div_cancel _ (pow_pos (pow_pos (by omega : 0<k) 2) 2)] at hc
  nlinarith

theorem exists_ninthRadius (n : ℕ) : ∃ k : ℕ,2≤k ∧ n≤k^9 := by
  refine ⟨n+2,by omega,?_⟩
  exact (show n≤n+2 by omega).trans (le_self_pow (by omega) (by decide))

noncomputable def ninthRadius (n : ℕ) : ℕ := Nat.find (exists_ninthRadius n)

theorem ninthRadius_spec (n : ℕ) : 2≤ninthRadius n ∧ n≤(ninthRadius n)^9 :=
  Nat.find_spec (exists_ninthRadius n)

theorem ninthRadius_predecessor (n : ℕ) (h : 2<ninthRadius n) :
    (ninthRadius n-1)^9<n := by
  by_contra hn
  have hm := Nat.find_min' (exists_ninthRadius n)
    (show 2≤ninthRadius n-1 ∧ n≤(ninthRadius n-1)^9 by omega)
  change ninthRadius n≤ninthRadius n-1 at hm
  omega

/-- The internal ninth-root scale stays within a fixed factor for n>0. -/
theorem ninthRadius_power_le (n : ℕ) (hn : 0<n) : (ninthRadius n)^9≤512*n := by
  have hk := (ninthRadius_spec n).1
  by_cases he : ninthRadius n=2
  · rw [he]
    norm_num
    omega
  · have hp := ninthRadius_predecessor n (by omega)
    have hdouble : ninthRadius n≤2*(ninthRadius n-1) := by omega
    have hpow := Nat.pow_le_pow_left hdouble 9
    rw [mul_pow] at hpow
    norm_num at hpow
    nlinarith

noncomputable def momentDefaultOutput (G : V → V → Prop)
    (hG : CanonicalSegments.Acyclic G) : Finset (V × V) :=
  fourHopPackedOutput G hG ((ninthRadius (Fintype.card V))^3)
    (by have h := Nat.pow_le_pow_left (ninthRadius_spec (Fintype.card V)).1 3;norm_num at h;omega)

/-- Every cover, path-preprocessing and numerical scale is internal. The
output still follows the original raw greedy and its original stopping rule. -/
theorem momentDefaultOutput_spec (G : V → V → Prop) (hG : CanonicalSegments.Acyclic G) :
    let k := ninthRadius (Fintype.card V)
    momentDefaultOutput G hG ⊆ candidates G ∧
    (momentDefaultOutput G hG).card ≤
      (6*PathFour.height (k^3)+1)*Fintype.card V+512*Fintype.card V*k^2+2 ∧
    ∀ s t,Reachable G s t → ∃ q : DWalk s t,
      Allowed (augment G (momentDefaultOutput G hG)) q ∧ q.length≤7*k^3+2 :=
  fourHopPackedOutput_ninth_scale G hG _ (ninthRadius_spec _).1 (ninthRadius_spec _).2

end GreedyShortcuts.UniformChainPacking
