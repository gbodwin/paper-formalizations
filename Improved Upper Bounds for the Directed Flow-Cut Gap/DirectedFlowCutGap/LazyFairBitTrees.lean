import DirectedFlowCutGap.FiniteDrawTrees

/-!
# Lazy fair-bit realization of adaptive finite draws

Every primitive of the lowered tree is a literal fair bit. A word is generated
only when its rejection trial is reached; accepted trials do not generate the
remaining tape. Failed bounded rejection returns the declared legal zero.
The proved distributional error is retained rather than calling that output
uniform. The call bound accounts for every possible default-induced history.
-/
namespace DirectedFlowCutGap.LazyFairBitTrees
open scoped BigOperators ENNReal
open FairBitWords BitSamplerCoupling FiniteDrawTrees

/-- Binary trees use only the actual two-element bit primitive. -/
inductive Binary {A : Type} : FiniteDrawTrees.Tree A → Prop where
  | pure (a : A) : Binary (.pure a)
  | draw {next : Fin 2 → FiniteDrawTrees.Tree A} (h : ∀ a, Binary (next a)) :
      Binary (.draw 2 (by decide) next)

theorem binary_bind {A B : Type} {p : FiniteDrawTrees.Tree A} (hp : Binary p)
    (next : A → FiniteDrawTrees.Tree B) (hn : ∀ a, Binary (next a)) : Binary (FiniteDrawTrees.bind p next) := by
  induction hp with
  | pure a => exact hn a
  | draw h ih => exact .draw ih

theorem binary_map {A B : Type} {p : FiniteDrawTrees.Tree A} (hp : Binary p) (f : A → B) :
    Binary (FiniteDrawTrees.map f p) := binary_bind hp _ (fun a => .pure (f a))

/-- Actual little-endian word generation consumes exactly its reached bits. -/
def word : (b : ℕ) → FiniteDrawTrees.Tree (Bits b)
  | 0 => .pure ()
  | b + 1 => FiniteDrawTrees.bind (pick 2 (by decide)) (fun a => FiniteDrawTrees.map (fun t => (a,t)) (word b))

theorem word_within (b : ℕ) : Within b (word b) := by
  induction b with
  | zero => exact .pure 0 ()
  | succ b ih =>
      change Within (b+1) (FiniteDrawTrees.bind (pick 2 (by decide))
        (fun a => FiniteDrawTrees.map (fun t : Bits b => (a,t)) (word b)))
      simpa only [Nat.add_comm] using
        within_bind (within_pick 2 (by decide)) _ (fun a => within_map ih (fun t => (a,t)))

theorem word_binary (b : ℕ) : Binary (word b) := by
  induction b with
  | zero => exact .pure ()
  | succ b ih =>
      exact binary_bind (.draw (fun a => .pure a)) _
        (fun a => binary_map ih (fun t => (a,t)))

/-- One actually executed word, with its output/counters from the same decoder. -/
def rejection (n : ℕ) (hn : 0 < n) : ℕ → FiniteDrawTrees.Tree (DefaultOutput n)
  | 0 => .pure ⟨⟨0,hn⟩,true,0,0⟩
  | T + 1 => FiniteDrawTrees.bind (word (width n)) fun t =>
      let w := FairBitWords.run (width n) t
      let x : Fin (bucket n) := ⟨w.1, run_value_lt (width n) t⟩
      match accept n x with
      | some a => .pure ⟨a,false,1,w.2⟩
      | none => FiniteDrawTrees.map (fun r => ⟨r.value,r.failed,r.trials+1,w.2+r.bits⟩)
          (rejection n hn T)

theorem rejection_within (n : ℕ) (hn : 0 < n) (T : ℕ) :
    Within (T * width n) (rejection n hn T) := by
  induction T with
  | zero =>
      simp only [Nat.zero_mul, rejection]
      exact .pure 0 _
  | succ T ih =>
      have h : Within (width n + T * width n) (rejection n hn (T+1)) := by
        apply within_bind (word_within (width n))
        intro t
        dsimp only
        split
        · exact .pure _ _
        · exact within_map ih _
      simpa only [Nat.add_mul, one_mul, Nat.add_comm] using h

theorem rejection_binary (n : ℕ) (hn : 0 < n) (T : ℕ) :
    Binary (rejection n hn T) := by
  induction T with
  | zero => exact .pure _
  | succ T ih =>
      apply binary_bind (word_binary (width n))
      intro t
      dsimp only
      split
      · exact .pure _
      · exact binary_map ih _

/-- Every dynamic finite draw is replaced at the point where it is requested. -/
def lower {A : Type} (T : ℕ) : FiniteDrawTrees.Tree A → FiniteDrawTrees.Tree A
  | .pure a => .pure a
  | .draw n hn next => FiniteDrawTrees.bind (rejection n hn T) (fun r => lower T (next r.value))

theorem lower_binary {A : Type} (T : ℕ) (p : FiniteDrawTrees.Tree A) : Binary (lower T p) := by
  induction p with
  | pure a => exact .pure a
  | draw n hn next ih => exact binary_bind (rejection_binary n hn T) _ (fun r => ih r.value)

/-- Widths are bounded on every branch, including all legal default branches. -/
inductive WidthsLE {A : Type} (w : ℕ) : FiniteDrawTrees.Tree A → Prop where
  | pure (a : A) : WidthsLE w (.pure a)
  | draw {n : ℕ} {hn : 0 < n} {next : Fin n → FiniteDrawTrees.Tree A}
      (width_le : width n ≤ w) (children : ∀ a, WidthsLE w (next a)) :
      WidthsLE w (.draw n hn next)

theorem widths_bind {A B : Type} {w : ℕ} {p : FiniteDrawTrees.Tree A} (hp : WidthsLE w p)
    (next : A → FiniteDrawTrees.Tree B) (hn : ∀ a, WidthsLE w (next a)) :
    WidthsLE w (FiniteDrawTrees.bind p next) := by
  induction hp with
  | pure a => exact hn a
  | draw hw children ih => exact .draw hw ih

theorem widths_map {A B : Type} {w : ℕ} {p : FiniteDrawTrees.Tree A} (hp : WidthsLE w p) (f : A → B) :
    WidthsLE w (FiniteDrawTrees.map f p) := widths_bind hp _ (fun a => .pure (f a))

theorem width_mono {a b : ℕ} (h : a ≤ b) : width a ≤ width b := by
  have hm := Nat.log_mono_right (b := 2) h
  simp only [width, Nat.log2_eq_log_two]
  omega

theorem lower_within {A : Type} {p : FiniteDrawTrees.Tree A} {q w : ℕ}
    (hp : Within q p) (hw : WidthsLE w p) (T : ℕ) :
    Within (q * T * w) (lower T p) := by
  induction hp with
  | pure q a => exact .pure _ a
  | @draw q n hn next children ih =>
      cases hw with
      | draw hw childrenW =>
          have call := within_mono (rejection_within n hn T) (Nat.mul_le_mul_left T hw)
          have rest := within_bind call (fun r => lower T (next r.value))
            (fun r => ih r.value (childrenW r.value))
          simpa only [lower, Nat.add_mul, one_mul, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using rest

noncomputable section

/-- The fair-bit tree has the literal independent word law. -/
theorem word_law (b : ℕ) : ideal (word b) = bitsLaw b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      change law uniformDraw (FiniteDrawTrees.bind (pick 2 (by decide))
        (fun a => FiniteDrawTrees.map (fun t : Bits b => (a,t)) (word b))) =
        FinitePermutationSampler.independent (PMF.uniformOfFintype (Fin 2)) (bitsLaw b)
      rw [law_bind, law_pick]
      simp_rw [law_map]
      change (uniformDraw 2 _).bind (fun a => (ideal (word b)).map (fun t => (a,t))) = _
      rw [ih]
      rfl

/-- The full generated output, including actual consumed-word counters, has the
same law as the counted tape interpreter. No eager tail generation is executed. -/
theorem rejection_law (n : ℕ) (hn : 0 < n) (T : ℕ) :
    ideal (rejection n hn T) =
      (BoundedBitRejection.tapeLaw n T).map (@fallbackRun n T ⟨hn.ne'⟩) := by
  let : NeZero n := ⟨hn.ne'⟩
  induction T with
  | zero =>
      exact (PMF.pure_map (f := fallbackRun n 0) ()).symm
  | succ T ih =>
      simp only [rejection, ideal, law_bind]
      rw [show law uniformDraw (word (width n)) = bitsLaw (width n) from word_law _]
      change (bitsLaw (width n)).bind _ =
        (FinitePermutationSampler.independent (bitsLaw (width n))
          (BoundedBitRejection.tapeLaw n T)).map _
      change _ = (FinitePermutationSampler.independent (bitsLaw (width n))
        (BoundedBitRejection.tapeLaw n T)).map
        (fun t : Bits (width n) × BoundedBitRejection.Tape n T => fallbackRun n (T+1) (t.1,t.2))
      rw [FinitePermutationSampler.independent, PMF.map_bind]
      congr 1
      funext t
      rw [PMF.map_comp]
      simp only [BoundedBitRejection.run_word_eq]
      cases h : accept n (decode (width n) t) with
      | some a =>
          simp only [law, Function.comp_def, fallbackRun, BoundedBitRejection.run,
            BoundedBitRejection.run_word_eq, h, Option.getD_some, Option.isNone_some]
          exact (PMF.map_const (BoundedBitRejection.tapeLaw n T) _).symm
      | none =>
          rw [law_map]
          have ih' : law uniformDraw (rejection n hn T) =
              (BoundedBitRejection.tapeLaw n T).map (fallbackRun n T) := ih
          simp only [Function.comp_def, fallbackRun, BoundedBitRejection.run,
            BoundedBitRejection.run_word_eq, h]
          rw [ih', PMF.map_comp]
          rfl

theorem rejection_value_law (n : ℕ) (hn : 0 < n) (T : ℕ) :
    (ideal (rejection n hn T)).map DefaultOutput.value =
      @fallback n T ⟨hn.ne'⟩ := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [rejection_law n hn T, PMF.map_comp]
  exact fallbackRun_law n T

/-- Lowering executes the actual biased sampler at each current draw. -/
theorem lower_law {A : Type} (T : ℕ) (p : FiniteDrawTrees.Tree A) :
    ideal (lower T p) = actual T p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
      simp only [lower, ideal, law_bind]
      change (ideal (rejection n hn T)).bind (fun r => ideal (lower T (next r.value))) = _
      simp_rw [ih]
      calc
        _ = ((ideal (rejection n hn T)).map DefaultOutput.value).bind
            (fun a => actual T (next a)) :=
          (PMF.bind_map (ideal (rejection n hn T)) DefaultOutput.value
            (fun a => actual T (next a))).symm
        _ = _ := by
          rw [rejection_value_law]
          rfl

/-- The output is an actual all-bit computation, with its approximation error. -/
theorem lowered_event_le {A : Type} [Fintype A] {q : ℕ} {p : FiniteDrawTrees.Tree A}
    (hp : Within q p) (T : ℕ) (P : A → Prop) :
    FiniteAmplification.probability (ideal (lower T p)) P ≤
      FiniteAmplification.probability (ideal p) P + (q : ℝ) * ((1 : ℝ) / 2)^T := by
  rw [lower_law]
  exact event_le hp T P

theorem lowered_support_subset_ideal {A : Type} (T : ℕ) (p : FiniteDrawTrees.Tree A) :
    (ideal (lower T p)).support ⊆ (ideal p).support := by
  rw [lower_law]
  exact actual_support_subset_ideal T p

end
end DirectedFlowCutGap.LazyFairBitTrees
