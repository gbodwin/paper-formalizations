import DirectedFlowCutGap.SupportPrimitiveBounds
import DirectedFlowCutGap.SupportSearchInvariants

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic

theorem visit_all (P : Bits → Prop) (adjacency : List Bits) (es : List (Bits×Bits))
    (u : Bits) (xs : List Code) (hu : P u) (hx : ∀ x∈xs,P x.1) :
    ∀ x∈visit adjacency es u xs,P x.1 := by
  unfold visit
  cases lookup u xs with
  | some x => exact hx
  | none =>
    cases predecessor adjacency es u xs with
    | none => exact hx
    | some x =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact hu
      · exact hx y hy

theorem pass_all (P : Bits → Prop) (adjacency : List Bits) (es : List (Bits×Bits))
    (vs : List Bits) (xs : List Code) (hv : ∀ u∈vs,P u) (hx : ∀ x∈xs,P x.1) :
    ∀ x∈pass adjacency es vs xs,P x.1 := by
  induction vs generalizing xs with
  | nil => exact hx
  | cons u us ih =>
    exact ih (visit adjacency es u xs) (fun v h => hv v (by simp [h]))
      (visit_all P adjacency es u xs (hv u (by simp)) hx)

theorem rounds_all (P : Bits → Prop) (vs : List Bits) (adjacency : List Bits)
    (es : List (Bits×Bits)) (target : Bits) (fuel : List Bits)
    (hv : ∀ u∈vs,P u) (ht : P target) :
    ∀ x∈rounds vs adjacency es target fuel,P x.1 := by
  induction fuel with
  | nil =>
    intro x hx
    simp only [rounds,List.mem_singleton] at hx
    subst x
    exact ht
  | cons u us ih => exact pass_all P adjacency es vs _ hv ih

theorem pass_steps_le (W N L : ℕ) (adjacency : List Bits) (es : List (Bits×Bits))
    (vs : List Bits) (xs : List Code) (hv : ∀ u∈vs,WordBound W N u)
    (hx : ∀ x∈xs,WordBound W N x.1) (hs : ∀ e∈es,EdgeWidths W e)
    (hL : xs.length+vs.length ≤ L) :
    passSteps adjacency es vs xs ≤ vs.length*(L*scanCap es.length W N+40)+3 := by
  induction vs generalizing xs with
  | nil => simp [passSteps]
  | cons u us ih =>
    have hu := hv u (by simp)
    have hm := visit_length adjacency es u xs
    have hi := ih (visit adjacency es u xs) (fun v h => hv v (by simp [h]))
      (visit_all (WordBound W N) adjacency es u xs hu hx) (by simp only [List.length_cons] at hL;omega)
    have hb := visit_steps_le W N adjacency es u xs hu hx hs
    have hlen : xs.length ≤ L := by simp only [List.length_cons] at hL;omega
    have hmul := Nat.mul_le_mul_right (scanCap es.length W N) hlen
    simp only [passSteps,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem round_steps_le (W N L : ℕ) (vs : List Bits) (adjacency : List Bits)
    (es : List (Bits×Bits)) (target : Bits) (fuel : List Bits)
    (hv : ∀ u∈vs,WordBound W N u) (ht : WordBound W N target)
    (hs : ∀ e∈es,EdgeWidths W e) (hL : 1+fuel.length*vs.length ≤ L) :
    roundSteps vs adjacency es target fuel ≤
      fuel.length*(vs.length*(L*scanCap es.length W N+40)+12)+6 := by
  induction fuel with
  | nil => simp [roundSteps]
  | cons u us ih =>
    have hsmall : 1+us.length*vs.length ≤ L := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hL
      omega
    have hi := ih hsmall
    have len := rounds_length vs adjacency es target us
    have hb := pass_steps_le W N L adjacency es vs (rounds vs adjacency es target us)
      hv (rounds_all (WordBound W N) vs adjacency es target us hv ht) hs (by
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hL
        omega)
    simp only [roundSteps,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def searchCap (V S W N : ℕ) : ℕ :=
  V*(V*((1+V*V)*scanCap S W N+40)+12)+(1+V*V)*(32*W+27)+16

theorem search_steps_le (W N : ℕ) (vs : List Bits) (adjacency : List Bits)
    (es : List (Bits×Bits)) (sw target : Bits)
    (hv : ∀ u∈vs,WordBound W N u) (ht : WordBound W N target)
    (hw : sw.length ≤ W) (hs : ∀ e∈es,EdgeWidths W e) :
    searchSteps vs adjacency es sw target ≤ searchCap vs.length es.length W N := by
  have hr := round_steps_le W N (1+vs.length*vs.length) vs adjacency es target vs hv ht hs (le_refl _)
  have hl := rounds_length vs adjacency es target vs
  have hb := lookup_steps_le W sw (rounds vs adjacency es target vs) hw
    (fun x hx => (rounds_all (WordBound W N) vs adjacency es target vs hv ht x hx).1)
  have hm := Nat.mul_le_mul_right (32*W+27) hl
  have he : extractSteps (lookup sw (rounds vs adjacency es target vs)) ≤ 3 := by
    cases lookup sw (rounds vs adjacency es target vs) <;> simp [extractSteps]
  unfold searchSteps searchCap
  omega

end DirectedFlowCutGap.SupportRecoveryProgram
