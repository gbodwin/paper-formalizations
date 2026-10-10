import DirectedFlowCutGap.BinaryTapeTrees

/-! A branchwise bit-prefix budget for the actual retained binary tape,
including both loops and its complete ledger record. -/
namespace DirectedFlowCutGap.BinaryTapeBudget
set_option backward.isDefEq.respectTransparency false
open BinaryArithmetic BinarySamplerMetadata BinaryRetainedTape
open FiniteDrawTrees LazyFairBitTrees

def budget (m : ℕ) (fuel cutoff : Bits) : ℕ :=
  m*value fuel*(FairBitWords.width m+FairBitWords.width (value cutoff))

theorem drawIndex_binary (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) :
    Binary (drawIndex BinarySamplerTrees.bit fuel bound hb hN s) := by
  unfold drawIndex
  apply binary_bind (BinaryFullPrefix.binary bound fuel (by omega) s)
  intro r
  exact .pure _

theorem drawIndex_within (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) :
    Within (value fuel*FairBitWords.width N)
      (drawIndex BinarySamplerTrees.bit fuel bound hb hN s) := by
  subst N
  unfold drawIndex
  have h := BinaryFullPrefix.within bound fuel (by omega) s
  change Within (value fuel*FairBitWords.width (value bound)) _ at h
  apply within_bind (r := 0) h
  intro r
  exact .pure 0 _

theorem permutation_binary (fuel : Bits) {A : Type} (xs : List A)
    (bound : Bits) (hb : value bound=xs.length) (s : Ledger) :
    Binary (permutation BinarySamplerTrees.bit fuel xs bound hb s) := by
  induction xs generalizing bound s with
  | nil => exact .pure _
  | cons x xs ih =>
    simp only [permutation]
    apply binary_bind (drawIndex_binary fuel bound hb (by simp) s)
    intro j
    apply binary_bind (ih _ _ _)
    intro t
    exact .pure _

theorem permutation_within (fuel : Bits) {A : Type} (xs : List A)
    (bound : Bits) (hb : value bound=xs.length) (s : Ledger) :
    Within (xs.length*value fuel*FairBitWords.width xs.length)
      (permutation BinarySamplerTrees.bit fuel xs bound hb s) := by
  induction xs generalizing bound s with
  | nil => exact .pure _ _
  | cons x xs ih =>
    have h : Within (value fuel*FairBitWords.width (xs.length+1)+
        xs.length*value fuel*FairBitWords.width xs.length)
        (permutation BinarySamplerTrees.bit fuel (x::xs) bound hb s) := by
      rw [permutation]
      apply within_bind (drawIndex_within fuel bound hb (by simp) s)
      intro j
      apply within_bind (r := 0) (ih _ _ _)
      intro t
      exact .pure 0 _
    apply within_mono h
    have hw : FairBitWords.width xs.length≤FairBitWords.width (xs.length+1) :=
      Nat.add_le_add_right (by
        by_cases hz : xs.length=0
        · simp [hz]
        · exact (Nat.le_log2 (by omega : xs.length+1 ≠ 0)).2
            ((Nat.log2_self_le hz).trans (Nat.le_succ _))) 1
    have hm := Nat.mul_le_mul_left (xs.length*value fuel) hw
    simp only [List.length_cons]
    nlinarith

theorem cells_binary (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (s : Ledger) :
    Binary (cells BinarySamplerTrees.bit fuel cutoff hcut hL xs s) := by
  induction xs generalizing s with
  | nil => exact .pure _
  | cons x xs ih =>
    rw [cells]
    apply binary_bind (drawIndex_binary fuel cutoff hcut hL s)
    intro j
    apply binary_bind (ih _)
    intro t
    exact .pure _

theorem cells_within (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (s : Ledger) :
    Within (xs.length*value fuel*FairBitWords.width L)
      (cells BinarySamplerTrees.bit fuel cutoff hcut hL xs s) := by
  induction xs generalizing s with
  | nil => exact .pure _ _
  | cons x xs ih =>
    have h : Within (value fuel*FairBitWords.width L+xs.length*value fuel*FairBitWords.width L)
        (cells BinarySamplerTrees.bit fuel cutoff hcut hL (x::xs) s) := by
      rw [cells]
      apply within_bind (drawIndex_within fuel cutoff hcut hL s)
      intro j
      apply within_bind (r := 0) (ih _)
      intro t
      exact .pure 0 _
    apply within_mono h
    simp only [List.length_cons]
    nlinarith

theorem tape_binary (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (bound : Bits)
    (hb : value bound=xs.length) (s : Ledger) :
    Binary (tape BinarySamplerTrees.bit fuel cutoff hcut hL xs bound hb s) := by
  unfold tape
  apply binary_bind (permutation_binary fuel xs bound hb s)
  intro p
  apply binary_bind (cells_binary fuel cutoff hcut hL xs p.2)
  intro c
  exact .pure _

theorem tape_within (fuel cutoff : Bits) {L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) {A : Type} (xs : List A) (bound : Bits)
    (hb : value bound=xs.length) (s : Ledger) :
    Within (budget xs.length fuel cutoff)
      (tape BinarySamplerTrees.bit fuel cutoff hcut hL xs bound hb s) := by
  have h : Within (xs.length*value fuel*FairBitWords.width xs.length+
      xs.length*value fuel*FairBitWords.width L)
      (tape BinarySamplerTrees.bit fuel cutoff hcut hL xs bound hb s) := by
    unfold tape
    apply within_bind (permutation_within fuel xs bound hb s)
    intro p
    apply within_bind (r := 0) (cells_within fuel cutoff hcut hL xs p.2)
    intro c
    exact .pure 0 _
  simpa only [budget,hcut,Nat.mul_add] using h

theorem sampleTape_binary (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    Binary (sampleTape BinarySamplerTrees.bit fuel cutoff hcut hL a s) := by
  unfold sampleTape
  apply binary_bind (tape_binary fuel cutoff hcut hL _ _ _ _)
  intro r
  exact .pure _

theorem sampleTape_within (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    Within (budget (RetainedTapeInput.activeList a).length fuel cutoff)
      (sampleTape BinarySamplerTrees.bit fuel cutoff hcut hL a s) := by
  unfold sampleTape
  apply within_bind (r := 0) (tape_within fuel cutoff hcut hL _ _ _ _)
  intro r
  exact .pure 0 _

theorem callback_binary (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    Binary ((callback BinarySamplerTrees.bit fuel cutoff hcut hL a).run s) := by
  simp only [callback,StateT.run]
  apply binary_bind (sampleTape_binary fuel cutoff hcut hL a _)
  intro r
  exact .pure _

theorem callback_within (fuel cutoff : Bits) {n L : ℕ} (hcut : value cutoff=L)
    (hL : 0<L) (a : RetainedGridState.PairFlags n) (s : Ledger) :
    Within (budget (RetainedTapeInput.activeList a).length fuel cutoff)
      ((callback BinarySamplerTrees.bit fuel cutoff hcut hL a).run s) := by
  simp only [callback,StateT.run]
  apply within_bind (r := 0) (sampleTape_within fuel cutoff hcut hL a _)
  intro r
  exact .pure 0 _

end DirectedFlowCutGap.BinaryTapeBudget
