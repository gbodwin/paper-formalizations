import DirectedFlowCutGap.BinaryTrackedPrefix

/-! A reasoning tree for the full actual binary sampler record. The interpreter
commutes with the original binary program, including its literal bits and
operation instrumentation. No tree is materialized by the executable sampler. -/
namespace DirectedFlowCutGap.BinarySamplerTrees
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinaryCounters BinaryBoundedSampler FiniteDrawTrees LazyFairBitTrees

def bit : FiniteDrawTrees.Tree Bool := .draw 2 (by decide) (fun i => .pure (decide (i.val=1)))

theorem bit_within : Within 1 bit := .draw (fun _ => .pure 0 _)
theorem bit_binary : Binary bit := .draw (fun _ => .pure _)

section Execute
variable {M : Type → Type} [Monad M] [LawfulMonad M]
variable (sample : (n : ℕ) → 0<n → M (Fin n))

theorem word_execute (count : Bits) :
    execute sample (BinaryRandomWord.word bit count) =
      BinaryRandomWord.word (execute sample bit) count := by
  have aux : ∀ n, ∀ c : Bits, value c=n →
      execute sample (BinaryRandomWord.word bit c) =
        BinaryRandomWord.word (execute sample bit) c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      conv_lhs => rw [BinaryRandomWord.word]
      conv_rhs => rw [BinaryRandomWord.word]
      split_ifs with hz
      · rfl
      · have hp := (predecessor_spec c).1
        have hv : 0<value c := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec c).1.mpr he))
        have hi := ih (value (predecessor c).1) (by rw [hp,←hc];omega) (predecessor c).1 rfl
        change execute sample (FiniteDrawTrees.bind bit _) = _
        rw [MonadicBitSampler.execute_bind]
        congr 1
        funext b
        change execute sample (FiniteDrawTrees.bind (BinaryRandomWord.word bit (predecessor c).1) _) = _
        rw [MonadicBitSampler.execute_bind,hi]
        rfl
  exact aux (value count) count rfl

theorem draw_execute (bound fuel : Bits) (positive : 0<value bound) :
    execute sample (BinaryBoundedSampler.draw bit bound positive fuel) =
      BinaryBoundedSampler.draw (execute sample bit) bound positive fuel := by
  have aux : ∀ n, ∀ f : Bits, value f=n →
      execute sample (BinaryBoundedSampler.draw bit bound positive f) =
        BinaryBoundedSampler.draw (execute sample bit) bound positive f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      conv_lhs => rw [BinaryBoundedSampler.draw]
      conv_rhs => rw [BinaryBoundedSampler.draw]
      split_ifs with hz
      · rfl
      · have hp := (predecessor_spec f).1
        have hv : 0<value f := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec f).1.mpr he))
        have hi := ih (value (predecessor f).1) (by rw [hp,←hf];omega) (predecessor f).1 rfl
        dsimp only
        change execute sample (FiniteDrawTrees.bind (BinaryRandomWord.word bit (sizeBits bound).1) _) = _
        rw [MonadicBitSampler.execute_bind,word_execute]
        congr 1
        funext x
        split_ifs with hx
        · rfl
        · change execute sample (FiniteDrawTrees.bind (BinaryBoundedSampler.draw bit bound positive (predecessor f).1) _) = _
          rw [MonadicBitSampler.execute_bind,hi]
          rfl
  exact aux (value fuel) fuel rfl
end Execute

theorem word_within (count : Bits) :
    Within (value count) (BinaryRandomWord.word bit count) := by
  have aux : ∀ n, ∀ c : Bits, value c=n → Within (value c) (BinaryRandomWord.word bit c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      rw [BinaryRandomWord.word]
      split_ifs with hz
      · exact .pure _ _
      · have hp := (predecessor_spec c).1
        have hv : 0<value c := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec c).1.mpr he))
        have hi := ih (value (predecessor c).1) (by rw [hp,←hc];omega) (predecessor c).1 rfl
        have he : value c=1+value (predecessor c).1 := by rw [hp];omega
        rw [he]
        apply within_bind bit_within
        intro b
        change Within (value (predecessor c).1)
          (FiniteDrawTrees.bind (BinaryRandomWord.word bit (predecessor c).1) _)
        apply within_bind (r := 0) hi
        intro r
        exact .pure 0 _
  exact aux (value count) count rfl

theorem word_binary (count : Bits) : Binary (BinaryRandomWord.word bit count) := by
  have aux : ∀ n, ∀ c : Bits, value c=n → Binary (BinaryRandomWord.word bit c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc
      rw [BinaryRandomWord.word]
      split_ifs with hz
      · exact .pure _
      · have hp := (predecessor_spec c).1
        have hv : 0<value c := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec c).1.mpr he))
        have hi := ih (value (predecessor c).1) (by rw [hp,←hc];omega) (predecessor c).1 rfl
        exact binary_bind bit_binary _ (fun _ => binary_bind hi _ (fun _ => .pure _))
  exact aux (value count) count rfl

theorem draw_within (bound fuel : Bits) (positive : 0<value bound) :
    Within (value fuel*FairBitWords.width (value bound))
      (BinaryBoundedSampler.draw bit bound positive fuel) := by
  have aux : ∀ n, ∀ f : Bits, value f=n →
      Within (value f*FairBitWords.width (value bound))
        (BinaryBoundedSampler.draw bit bound positive f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      rw [BinaryBoundedSampler.draw]
      split_ifs with hz
      · exact .pure _ _
      · have hp := (predecessor_spec f).1
        have hv : 0<value f := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec f).1.mpr he))
        have hi := ih (value (predecessor f).1) (by rw [hp,←hf];omega) (predecessor f).1 rfl
        have hw := (sizeBits_spec bound).1.trans (BinaryBoundedSampler.size_eq_width positive)
        have he : value f*FairBitWords.width (value bound) =
            value (sizeBits bound).1+value (predecessor f).1*FairBitWords.width (value bound) := by
          rw [hw,hp]; have hh : value f=value f-1+1 := by omega
          conv_lhs => rw [hh]
          ring
        rw [he]
        apply within_bind (word_within (sizeBits bound).1)
        intro x
        dsimp only
        split_ifs with hx
        · exact .pure _ _
        · change Within (value (predecessor f).1*FairBitWords.width (value bound))
            (FiniteDrawTrees.bind (BinaryBoundedSampler.draw bit bound positive (predecessor f).1) _)
          apply within_bind (r := 0) hi
          intro r
          exact .pure 0 _
  exact aux (value fuel) fuel rfl

theorem draw_binary (bound fuel : Bits) (positive : 0<value bound) :
    Binary (BinaryBoundedSampler.draw bit bound positive fuel) := by
  have aux : ∀ n, ∀ f : Bits, value f=n →
      Binary (BinaryBoundedSampler.draw bit bound positive f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf
      rw [BinaryBoundedSampler.draw]
      split_ifs with hz
      · exact .pure _
      · have hp := (predecessor_spec f).1
        have hv : 0<value f := Nat.pos_of_ne_zero
          (fun he => hz ((isZero_spec f).1.mpr he))
        have hi := ih (value (predecessor f).1) (by rw [hp,←hf];omega) (predecessor f).1 rfl
        apply binary_bind (word_binary (sizeBits bound).1)
        intro x
        dsimp only
        split_ifs with hx
        · exact .pure _
        · exact binary_bind hi _ (fun _ => .pure _)
  exact aux (value fuel) fuel rfl

end DirectedFlowCutGap.BinarySamplerTrees
