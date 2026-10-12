import DirectedFlowCutGap.ScalarQuotientRowProgram

namespace DirectedFlowCutGap.ScalarQuotientRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem divide_head (mode : Bool) (scalar x : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (head : Stored heap a x) (sc : Stored heap b scalar) (next tail : ℕ)
    (hn : next=heap.length) (stack : List (Frame ℕ 182)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalQuotient.cells (numerator mode scalar x) (denominator mode scalar x) ∧
      NaturalRun (program mode)
        (CanonicalRationalQuotient.steps (numerator mode scalar x) (denominator mode scalar x)+
          (if mode then 6 else 3))
        (state heap next a b tail tail stack source 172) []
        (state (heap++ext) (next+ext.length) (if mode then b else a)
          (if mode then a else b) tail root stack source 176) ∧
      Stored (heap++ext) root
        (BinaryRational.div (numerator mode scalar x) (denominator mode scalar x)).1 := by
  cases mode with
  | false =>
    obtain ⟨ext,root,len,body,rep⟩ := quotient_return false x scalar head sc next tail tail hn
      ⟨a,b,tail,tail⟩ 176 stack source
    have call : tickNatural (program false) (state heap next a b tail tail stack source 172)=
        some ⟨state heap next a b tail tail (⟨176,.r3,⟨a,b,tail,tail⟩⟩::stack) source 161,[],0⟩ := by
      simp [tickNatural,program,state]
    refine ⟨ext,root,len,?_,rep⟩
    convert NaturalRun.step call body using 1 <;> simp [numerator,denominator]
  | true =>
    obtain ⟨ext,root,len,body,rep⟩ := quotient_return true scalar x sc head next tail a hn
      ⟨b,a,tail,a⟩ 176 stack source
    have t172 : tickNatural (program true) (state heap next a b tail tail stack source 172)=
        some ⟨state heap next a b tail a stack source 173,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t173 : tickNatural (program true) (state heap next a b tail a stack source 173)=
        some ⟨state heap next b b tail a stack source 174,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t174 : tickNatural (program true) (state heap next b b tail a stack source 174)=
        some ⟨state heap next b a tail a stack source 175,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    have t175 : tickNatural (program true) (state heap next b a tail a stack source 175)=
        some ⟨state heap next b a tail a (⟨176,.r3,⟨b,a,tail,a⟩⟩::stack) source 161,[],0⟩ := by
      simp [tickNatural,program,state]
    refine ⟨ext,root,len,?_,rep⟩
    convert NaturalRun.step t172 (.step t173 (.step t174 (.step t175 body))) using 1 <;>
      simp [numerator,denominator]
end DirectedFlowCutGap.ScalarQuotientRow
