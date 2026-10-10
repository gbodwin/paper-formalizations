import GreedyShortcuts.SCCBudget

/-! A finite all-target SCC bound before asymptotic regime absorption. -/
namespace GreedyShortcuts.SCCGeneral
open DirectedPaths DAGProgress
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem output_card_any (G : V → V → Prop) (b : ℕ) (hb : 1 ≤ b) :
    (SCCGreedy.output G b hb).card ≤
      (Nat.log 2 ((Fintype.card V)^3)+1)*132000*(Fintype.card V+(Fintype.card V)^2/b^3+1) := by
  let n := Fintype.card V
  let q := Fintype.card (SCCQuotient.Component G)
  let d := n^2/b^3
  let k := Nat.log 2 (n^3)+1
  have hq : q ≤ n := SCCQuotient.component_card G
  have hk : 1 ≤ k := by dsimp [k];omega
  change (SCCGreedy.output G b hb).card ≤ k*132000*(n+d+1)
  by_cases hb8 : 8 ≤ b
  · have hd := DAGProgress.output_card_bound (SCCQuotient.acyclic G) b 8 hb8 (by omega)
    have hlog : Nat.log 2 (q^3)+1 ≤ k := Nat.add_le_add_right
      (Nat.log_mono_right (Nat.pow_le_pow_left hq 3)) 1
    have hblock : blockLength q b 8 ≤ 131072*(n+d+1)+1 := by
      unfold blockLength
      apply max_le
      · have hh := Nat.div_le_self (512*q) 8
        nlinarith
      · have hnum : 16384*8*q^2 ≤ 131072*n^2 := by nlinarith [Nat.pow_le_pow_left hq 2]
        have hd' := (Nat.div_le_div_right (c:=b^3) hnum).trans
          (SCCBudget.scaled_div (C:=131072) (a:=n^2) (by positivity : 0 < b^3))
        change 16384*8*q^2/b^3 ≤ 131072*(d+1) at hd'
        omega
    have hgreedy := hd.trans (Nat.mul_le_mul hlog hblock)
    have hcard := SCCGreedy.output_card_le G b hb
    change (SCCGreedy.output G b hb).card ≤ 2*n+_ at hcard
    have hkn := Nat.mul_le_mul_right (2*n) hk
    nlinarith
  · have hb7 : b ≤ 7 := by omega
    have hb3 : b^3 ≤ 343 := by nlinarith [Nat.pow_le_pow_left hb7 3]
    have hrem := Nat.mod_lt (n^2) (by positivity : 0 < b^3)
    have he := Nat.mod_add_div (n^2) (b^3)
    have hstep : n^2 ≤ b^3*(d+1) := by dsimp [d];nlinarith
    have hbase : n^2 ≤ 343*(d+1) := hstep.trans (Nat.mul_le_mul_right _ hb3)
    have hcard : (SCCGreedy.output G b hb).card ≤ n^2 := by
      calc
        _ ≤ (candidates G).card := Finset.card_le_card (SCCGreedy.output_legal G b hb)
        _ ≤ Fintype.card (V × V) := Finset.card_le_univ _
        _ = n^2 := by simp [n,pow_two]
    have hmul := Nat.mul_le_mul_right (132000*(n+d+1)) hk
    nlinarith


theorem target_card_any (G : V → V → Prop) (B : ℕ) (hB : 5≤B) :
    (SCCGreedy.output G ((B-2)/3) (by omega)).card ≤
      45408000*(Nat.log 2 ((Fintype.card V)^3)+1)*
        (Fintype.card V+(Fintype.card V)^2/B^3+1) := by
  let n := Fintype.card V
  let b := (B-2)/3
  let d := n^2/b^3
  let e := n^2/B^3
  let k := Nat.log 2 (n^3)+1
  have hb : 1≤b := by dsimp [b];omega
  have hBb : B≤7*b := by dsimp [b];omega
  have hpow : B^3≤343*b^3 := by nlinarith [Nat.pow_le_pow_left hBb 3]
  have hstep : n^2≤B^3*(e+1) := by
    have hrem := Nat.mod_lt (n^2) (by positivity : 0<B^3)
    have he := Nat.mod_add_div (n^2) (B^3)
    dsimp [e]
    nlinarith
  have hnum : n^2 ≤ (343*(e+1))*b^3 := by
    have hh := hstep.trans (Nat.mul_le_mul_right (e+1) hpow)
    nlinarith
  have hde : d ≤ 343*(e+1) := by
    have hh := Nat.div_le_div_right (c:=b^3) hnum
    simpa [Nat.mul_div_cancel _ (by positivity : 0<b^3)] using hh
  have hh := output_card_any G b hb
  change (SCCGreedy.output G b hb).card ≤ k*132000*(n+d+1) at hh
  change (SCCGreedy.output G b hb).card ≤ 45408000*k*(n+e+1)
  calc
    _ ≤ k*132000*(n+d+1) := hh
    _ ≤ k*132000*(344*(n+e+1)) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by ring

end GreedyShortcuts.SCCGeneral
