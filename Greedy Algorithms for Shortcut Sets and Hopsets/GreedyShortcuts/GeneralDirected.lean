import GreedyShortcuts.KernelRegimes
import GreedyShortcuts.SCCGeneral

/-! Actual general-directed shortcut construction with an unconditional finite
all-regime cardinality bound. It combines concrete deterministic kernel
preprocessing, the proved DAG greedy algorithm, and the actual SCC fallback. -/
namespace GreedyShortcuts.GeneralDirected
open DirectedPaths KernelSamplingBalance
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def output (G : V → V → Prop) (B : ℕ) (hB : 1≤B) : Finset (V × V) := by
  classical
  let n := Fintype.card V
  let b := parameter n B
  exact if n≤B then ∅ else if h5 : 5≤B then
    if b^3≤logarithm n*n then KernelSamplingBalance.output G b (by have := parameter_ge n B;omega)
    else SCCGreedy.output G ((B-2)/3) (by omega)
  else GraphGreedy.output G B hB

theorem output_legal (G : V → V → Prop) (B : ℕ) (hB : 1≤B) :
    output G B hB ⊆ candidates G := by
  classical
  unfold output
  dsimp only
  split_ifs
  · exact Finset.empty_subset _
  · exact KernelSamplingBalance.output_legal G _ _
  · exact SCCGreedy.output_legal G _ _
  · exact GraphGreedy.output_subset G B hB

theorem output_card_quadratic (G : V → V → Prop) (B : ℕ) (hB : 1≤B) :
    (output G B hB).card ≤ (Fintype.card V)^2 := by
  calc
    _ ≤ (candidates G).card := Finset.card_le_card (output_legal G B hB)
    _ ≤ Fintype.card (V × V) := Finset.card_le_univ _
    _ = _ := by simp [pow_two]

theorem output_hop (G : V → V → Prop) (B : ℕ) (hB : 1≤B)
    {s t : V} (hr : Reachable G s t) : hopDist (augment G (output G B hB)) s t ≤ B := by
  classical
  unfold output
  dsimp only
  split_ifs with hn h5 hreg
  · have he : augment G (∅ : Finset (V × V)) = G := by funext u v;simp [augment]
    rw [he]
    exact (hopDist_le_card G s t).trans hn
  · exact KernelSamplingBalance.target_hop G B (by omega) hreg hr
  · exact SCCGreedy.target_hop_bound G B h5 hr
  · exact GraphGreedy.output_hop_bound G B hB hr

def kernelTerm (n B : ℕ) : ℕ :=
  (Nat.log 2 ((parameter n B)^9)+1)*
    (131074*((8+2*logarithm n)^3+(Nat.sqrt (42*logarithm n*n/B)+1)^3)+1)

def bound (n B : ℕ) : ℕ := kernelTerm n B+1000000*(logarithm n)^4+
  216000000000000*logarithm n*(Nat.log 2 (n^3)+1)*(n^2/B^3+1)

theorem parameter_cube (n B : ℕ) :
    (parameter n B)^3 ≤ (8+2*logarithm n)^3+(Nat.sqrt (42*logarithm n*n/B)+1)^3 := by
  unfold parameter
  rcases le_total (8+2*logarithm n) (Nat.sqrt (42*logarithm n*n/B)+1) with h | h
  · rw [max_eq_right h];omega
  · rw [max_eq_left h];omega

theorem tiny_target_bound (n B : ℕ) (hB : 1≤B) (hsmall : B<5) :
    n^2 ≤ 216000000000000*logarithm n*(Nat.log 2 (n^3)+1)*(n^2/B^3+1) := by
  let q := n^2/B^3
  have hk : 1≤logarithm n := by unfold logarithm;omega
  have hl : 1≤Nat.log 2 (n^3)+1 := by omega
  have hp : B^3≤64 := by nlinarith [Nat.pow_le_pow_left (by omega : B≤4) 3]
  have hstep : n^2≤B^3*(q+1) := by
    have hm := Nat.mod_lt (n^2) (by positivity : 0<B^3)
    have he := Nat.mod_add_div (n^2) (B^3)
    dsimp [q]
    nlinarith
  have hn : n^2≤64*(q+1) := hstep.trans (Nat.mul_le_mul_right _ hp)
  have hc : 64≤216000000000000*logarithm n*(Nat.log 2 (n^3)+1) := by nlinarith
  exact hn.trans (Nat.mul_le_mul_right _ hc)

theorem scc_absorb (G : V → V → Prop) (B : ℕ) (hB : 5≤B)
    (hscale : B^3≤4741632*logarithm (Fintype.card V)*Fintype.card V) :
    (SCCGreedy.output G ((B-2)/3) (by omega)).card ≤
      216000000000000*logarithm (Fintype.card V)*(Nat.log 2 ((Fintype.card V)^3)+1)*
        ((Fintype.card V)^2/B^3+1) := by
  let n := Fintype.card V
  let k := logarithm n
  let l := Nat.log 2 (n^3)+1
  let q := n^2/B^3
  have hk : 1≤k := by dsimp [k,logarithm];omega
  have hnum : n*B^3 ≤ (4741632*k)*n^2 := by
    have hh := Nat.mul_le_mul_left n hscale
    change n*B^3 ≤ n*(4741632*k*n) at hh
    nlinarith
  have hnq : n≤(4741632*k)* (q+1) := by
    have hdiv := (Nat.le_div_iff_mul_le (by positivity : 0<B^3)).mpr hnum
    exact hdiv.trans (SCCBudget.scaled_div (C:=4741632*k) (a:=n^2) (by positivity : 0<B^3))
  have hsum : n+q+1 ≤ (4741633*k)*(q+1) := by nlinarith
  have hc : 45408000*l*((4741633*k)*(q+1)) ≤ 216000000000000*k*l*(q+1) := by
    have hcoef : 45408000*4741633 ≤ (216000000000000 : ℕ) := by decide
    have hh := Nat.mul_le_mul_right (k*l*(q+1)) hcoef
    nlinarith
  exact (SCCGeneral.target_card_any G B hB).trans
    ((Nat.mul_le_mul_left (45408000*l) hsum).trans hc)

/-- Every hypothesis is an original finite graph or positive target; the
kernel, its geometry, progress and all regime choices are constructed. -/
theorem output_card (G : V → V → Prop) (B : ℕ) (hB : 1≤B) :
    (output G B hB).card ≤ bound (Fintype.card V) B := by
  classical
  let n := Fintype.card V
  let k := logarithm n
  let b := parameter n B
  have hquad : (output G B hB).card ≤ n^2 := output_card_quadratic G B hB
  change (output G B hB).card ≤ bound n B
  have hterm : kernelTerm n B ≤ bound n B := by unfold bound;omega
  have hsmallterm : 1000000*k^4 ≤ bound n B := by dsimp [k];unfold bound;omega
  have hcubicterm : 216000000000000*logarithm n*(Nat.log 2 (n^3)+1)*(n^2/B^3+1) ≤ bound n B := by
    unfold bound;omega
  by_cases hn : n≤B
  · have hn' : Fintype.card V ≤ B := hn
    simp only [output,ite_eq_left hn',Finset.card_empty]
    exact Nat.zero_le _
  by_cases h5 : 5≤B
  · by_cases hreg : b^3≤k*n
    · have hh := KernelSamplingBalance.output_card G b (parameter_ge n B) (parameter_budget n B)
      have hp := parameter_cube n B
      change b^3 ≤ _ at hp
      have ht : (KernelSamplingBalance.output G b (by have := parameter_ge n B;omega)).card ≤
          kernelTerm n B := by
        exact hh.trans (Nat.mul_le_mul_left _ (by omega))
      have hout : output G B hB = KernelSamplingBalance.output G b
          (by have := parameter_ge n B;omega) := by
        unfold output
        dsimp only
        rw [ite_eq_right (show ¬Fintype.card V≤B from hn),dite_eq_left h5,
          ite_eq_left (show parameter (Fintype.card V) B ^ 3 ≤ logarithm (Fintype.card V)*Fintype.card V from hreg)]
      rw [hout]
      exact ht.trans hterm
    · have hlarge : logarithm n*n < (parameter n B)^3 := by change k*n < b^3;omega
      rcases KernelRegimes.parameter_large_split n B hlarge with hsmall | hlarge
      · have hpow : n^2≤1000000*k^4 := by
          have hh := Nat.pow_le_pow_left hsmall 2
          simpa [← pow_mul,mul_pow,k] using hh
        exact hquad.trans (hpow.trans hsmallterm)
      · have hh := scc_absorb G B h5 hlarge
        have hout : output G B hB = SCCGreedy.output G ((B-2)/3) (by omega) := by
          unfold output
          dsimp only
          rw [ite_eq_right (show ¬Fintype.card V≤B from hn),dite_eq_left h5,
            ite_eq_right (show ¬parameter (Fintype.card V) B ^ 3 ≤ logarithm (Fintype.card V)*Fintype.card V from hreg)]
        rw [hout]
        exact hh.trans hcubicterm
  · exact hquad.trans ((tiny_target_bound n B hB (by omega)).trans hcubicterm)

end GreedyShortcuts.GeneralDirected
