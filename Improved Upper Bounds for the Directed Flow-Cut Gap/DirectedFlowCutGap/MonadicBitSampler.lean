import DirectedFlowCutGap.LazyFairBitTrees

/-!
# Direct monadic bounded-bit decoding

The executable callback reads a bit and decodes it in the same recursion. It
constructs no binary-word tape and requests no unvisited rejection tail.
The refinement is an equality in every lawful monad, so it preserves a StateM
bit position as well as the returned value and counters. Arithmetic charges
and the adaptive tape materializer are separate layers.
-/
namespace DirectedFlowCutGap.MonadicBitSampler
open FairBitWords BitSamplerCoupling FiniteDrawTrees LazyFairBitTrees

variable {m : Type → Type} [Monad m]

/-- Only the binary branch is reached by a proved Binary tree. -/
def liftBit (bit : m (Fin 2)) (n : ℕ) (hn : 0<n) : m (Fin n) :=
  if h : n=2 then h.symm ▸ bit else pure ⟨0,hn⟩

@[simp] theorem liftBit_two (bit : m (Fin 2)) (hn : 0<2) :
    liftBit bit 2 hn = bit := by simp [liftBit]

/-- Positional decoding fused with the requests for the actual bits. -/
def wordValue (bit : m (Fin 2)) : (b : ℕ) → m (Fin (2^b))
  | 0 => pure 0
  | b+1 => do
      let a ← bit
      let t ← wordValue bit b
      pure ⟨2*t.val+a.val, by
        have ha := a.isLt
        have ht := t.isLt
        rw [pow_succ]
        omega⟩

/-- Explicit failure remains observable even though the returned index is legal. -/
def draw (bit : m (Fin 2)) (n : ℕ) (hn : 0<n) : ℕ → m (DefaultOutput n)
  | 0 => pure ⟨⟨0,hn⟩,true,0,0⟩
  | T+1 => do
      let x ← wordValue bit (width n)
      if hx : x.val<n then pure ⟨⟨x.val,hx⟩,false,1,width n⟩ else
        let r ← draw bit n hn T
        pure ⟨r.value,r.failed,r.trials+1,width n+r.bits⟩

/-- The callback consumed by an arbitrary adaptive finite-draw interpreter. -/
def sample (bit : m (Fin 2)) (T n : ℕ) (hn : 0<n) : m (Fin n) := do
  let r ← draw bit n hn T
  pure r.value

section Lawful
variable [LawfulMonad m]

theorem execute_bind (sample : (n : ℕ) → 0<n → m (Fin n))
    {A B : Type} (p : FiniteDrawTrees.Tree A) (next : A → FiniteDrawTrees.Tree B) :
    execute sample (FiniteDrawTrees.bind p next) = (do
      let a ← execute sample p
      execute sample (next a)) := by
  induction p with
  | pure a => simp [FiniteDrawTrees.bind,execute]
  | draw n hn rest ih =>
      simp only [FiniteDrawTrees.bind,execute,bind_assoc]
      congr 1
      funext a
      exact ih a

theorem execute_map (sample : (n : ℕ) → 0<n → m (Fin n))
    {A B : Type} (f : A → B) (p : FiniteDrawTrees.Tree A) :
    execute sample (FiniteDrawTrees.map f p) = (do
      let a ← execute sample p
      pure (f a)) := by
  rw [FiniteDrawTrees.map,execute_bind]
  rfl

@[simp] theorem execute_pick (sample : (n : ℕ) → 0<n → m (Fin n))
    (n : ℕ) (hn : 0<n) : execute sample (pick n hn) = sample n hn := by
  simp [pick,execute]

/-- This packages the checked arithmetic decoder with its proved range. -/
def decoded (b : ℕ) (t : Bits b) : Fin (2^b) :=
  ⟨(FairBitWords.run b t).1,run_value_lt b t⟩

theorem wordValue_refines (bit : m (Fin 2)) (b : ℕ) :
    wordValue bit b = execute (liftBit bit)
      (FiniteDrawTrees.map (decoded b) (LazyFairBitTrees.word b)) := by
  induction b with
  | zero => simp [wordValue,LazyFairBitTrees.word,FiniteDrawTrees.map,
      FiniteDrawTrees.bind,execute,decoded,FairBitWords.run]
  | succ b ih =>
      rw [wordValue,execute_map]
      change (bit >>= fun a => wordValue bit b >>= fun t =>
        pure (⟨2*t.val+a.val,by have ht := t.isLt;have ha := a.isLt;rw [pow_succ];omega⟩ : Fin (2^(b+1)))) =
        (execute (liftBit bit) (FiniteDrawTrees.bind (pick 2 (by decide))
          (fun a => FiniteDrawTrees.map (fun t : Bits b => (a,t)) (LazyFairBitTrees.word b))) >>= fun t =>
          pure (decoded (b+1) t))
      rw [execute_bind,execute_pick,liftBit_two,ih,execute_map]
      simp only [bind_assoc,pure_bind]
      congr 1
      funext a
      rw [execute_map]
      simp only [bind_assoc,pure_bind]
      congr 1

/-- Full callback refinement, including rejection flags and consumed counters. -/
theorem draw_refines (bit : m (Fin 2)) (n : ℕ) (hn : 0<n) (T : ℕ) :
    draw bit n hn T = execute (liftBit bit) (rejection n hn T) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [draw,rejection,execute_bind]
      rw [wordValue_refines,execute_map]
      simp only [bind_assoc,pure_bind]
      congr 1
      funext t
      dsimp only [decoded]
      by_cases h : (FairBitWords.run (width n) t).1<n
      · simp [h,accept,execute,FairBitWords.run_bits]
      · simp [h,accept,execute_map,ih,FairBitWords.run_bits]

/-- Equality in the supplied monad retains all callback state effects. -/
theorem execute_lower_refines (bit : m (Fin 2)) (T : ℕ)
    {A : Type} (p : FiniteDrawTrees.Tree A) :
    execute (liftBit bit) (lower T p) = execute (sample bit T) p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [lower,execute_bind]
      rw [← draw_refines (m := m)]
      simp only [execute,sample,bind_assoc]
      congr 1
      funext r
      simpa only [pure_bind] using ih r.value

end Lawful
end DirectedFlowCutGap.MonadicBitSampler
