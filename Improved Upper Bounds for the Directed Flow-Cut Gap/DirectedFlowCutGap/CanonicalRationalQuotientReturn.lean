import DirectedFlowCutGap.CanonicalRationalQuotientFinish

namespace DirectedFlowCutGap.CanonicalRationalQuotient
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem quotient_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 164)
    (stack : List (Frame ℕ 164)) (source : Bits) :
    ∃ ext root,ext.length=cells x y ∧
      NaturalRun program (steps x y)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 144) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.div x y).1 := by
  obtain ⟨yn,yd,record,num,den⟩ := right
  let frames : List (Frame ℕ 164) := ⟨pc,.r3,saved⟩::stack
  let e0 : NaturalHeap := [.pair a b,.flag (BinaryArithmetic.isZero y.num).1]
  let h0 := heap++e0
  let n0 := next+2
  have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
  have prefixRun := test_prefix (a:=a) record num next c d hn frames source
  have flag : h0[next+1]?=some (.flag (BinaryArithmetic.isZero y.num).1) := by simp [h0,e0,hn]
  have pair : h0[next]?=some (.pair a b) := by simp [h0,e0,hn]
  cases hz : (BinaryArithmetic.isZero y.num).1 with
  | true =>
    have flag' : h0[next+1]?=some (.flag true) := by simpa [hz] using flag
    obtain ⟨ez,rz,lz,finish,rep⟩ := zero_finish (a:=yn) (b:=b) (c:=next)
      flag' n0 dense0 saved pc stack source
    refine ⟨e0++ez,rz,by simp [e0,cells,hz,lz],?_,?_⟩
    · convert run_append prefixRun finish using 1 <;> simp [steps,hz,h0,n0,e0,state,List.append_assoc,Nat.add_assoc]
      all_goals omega
    · simpa [BinaryRational.div,hz,h0,List.append_assoc] using rep
  | false =>
    have flag' : h0[next+1]?=some (.flag false) := by simpa [hz] using flag
    have right' : Stored h0 b y := stored_extend ⟨yn,yd,record,num,den⟩ e0
    obtain ⟨ep,rp,lp,finish,rep⟩ := nonzero_finish x y hz (a:=yn) (b:=b) flag' pair
      (stored_extend left e0) right' n0 dense0 saved pc stack source
    refine ⟨e0++ep,rp,by simp [e0,cells,hz,lp],?_,?_⟩
    · convert run_append prefixRun finish using 1 <;> simp [steps,hz,h0,n0,e0,state,List.append_assoc,Nat.add_assoc]
      all_goals omega
    · simpa [h0,List.append_assoc] using rep
end DirectedFlowCutGap.CanonicalRationalQuotient
