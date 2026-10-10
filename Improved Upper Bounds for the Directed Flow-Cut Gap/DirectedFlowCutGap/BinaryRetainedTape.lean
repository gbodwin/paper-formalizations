import DirectedFlowCutGap.BinarySamplerMetadata
import DirectedFlowCutGap.RetainedFairBitLaw
import DirectedFlowCutGap.EncodedTapeMaterialization

/-!
# Retained-mask adapter for the actual bounded binary draws

The active list is constructed once. A fixed increment scan builds its binary
count, and both tape loops recurse on that retained list. No Fintype cardinality
or Nat.bits map is evaluated to control the sampler. Permutation bounds shrink
by the actual binary predecessor; all cell draws use the retained cutoff word.
The cutoff and rejection fuel are supplied binary inputs, with an erased cutoff
equality. Their construction at the outer natural-parameter boundary is open.

Every draw is the actual BinarySamplerMetadata.trackedDraw call. The literal
returned index is decoded once for the existing Fin-valued tape interface, and
its decoding charge is added to the same ledger. Failure, physical binary trial
and consumed-bit counters, and draw count all come from those same calls.

The active-list producer has the existing declared dictionary allowance. Its
row-major enumeration/filter representation certificate remains separate.
decodeIndex exposes the native shift/add conversion and its word charge; its
binary representation/copy realization remains explicit. The fixed count and
list-control bodies hide no host callback. Charges are mathematical
instrumentation; no native compiler erasure or allocator theorem is asserted.
The law comparison is to bounded rejection, never exact ideal uniformity.
-/
namespace DirectedFlowCutGap.BinaryRetainedTape
open BinaryArithmetic BinarySamplerMetadata RetainedGridState
open scoped NNReal

set_option backward.isDefEq.respectTransparency false

/-- One named binary increment per retained element. -/
def count {A : Type} : List A → Bits × ℕ
  | [] => ([],1)
  | _::xs =>
      let r := count xs
      let c := increment true r.1
      (c.1,r.2+c.2+8)

theorem count_spec {A : Type} (xs : List A) :
    value (count xs).1 = xs.length ∧
      (count xs).1.length ≤ xs.length ∧
      (count xs).2 ≤ 16*(xs.length+1)^2 := by
  induction xs with
  | nil => simp [count,value]
  | cons x xs ih =>
      have h := increment_spec true (count xs).1
      simp only [count,List.length_cons]
      refine ⟨?_,?_,?_⟩
      · simpa only [Bool.toNat_true,ih.1] using h.1
      · omega
      · nlinarith [h.2.2,ih.2.2]

/-- Closed count-body derivation, with no arbitrary host callback. -/
inductive CountExec {A : Type} : List A → Bits → ℕ → Prop
  | nil : CountExec [] [] 1
  | cons (x : A) (xs : List A) (b : Bits) (q : ℕ) :
      CountExec xs b q →
      CountExec (x::xs) (increment true b).1 (q+(increment true b).2+8)

theorem count_exec {A : Type} (xs : List A) :
    CountExec xs (count xs).1 (count xs).2 := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons x xs _ _ ih

theorem CountExec.result {A : Type} {xs : List A} {b : Bits} {q : ℕ}
    (h : CountExec xs b q) : b = (count xs).1 ∧ q = (count xs).2 := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs b q _ ih => simp only [count,ih.1,ih.2,and_self]

theorem CountExec.cost {A : Type} {xs : List A} {b : Bits} {q : ℕ}
    (h : CountExec xs b q) : q ≤ 16*(xs.length+1)^2 := by
  rw [h.result.2]
  exact (count_spec xs).2.2

theorem setup_bound {n : ℕ} (a : PairFlags n) :
    EncodedTapeMaterialization.dictionaryBound n+
      (count (RetainedTapeInput.activeList a)).2+16 ≤ 48*(n*n+1)^2+16 := by
  have hm : (RetainedTapeInput.activeList a).length ≤ n*n := by
    rw [RetainedTapeInput.activeList_length]
    exact RetainedDrawTrees.active_card_le a
  have hc := (count_spec (RetainedTapeInput.activeList a)).2.2
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2
  unfold EncodedTapeMaterialization.dictionaryBound
  nlinarith

/-- Executed conversion, not an unpriced proof-side denotation. Eight words
pay the bit case, native shift/add, pair and loop control. Bit realization of
these native operations is a named remaining representation obligation. -/
def decodeIndex : Bits → ℕ × ℕ
  | [] => (0,1)
  | b::bs =>
      let r := decodeIndex bs
      (b.toNat+2*r.1,r.2+8)

theorem decodeIndex_spec (bs : Bits) :
    (decodeIndex bs).1 = value bs ∧ (decodeIndex bs).2 = 8*bs.length+1 := by
  induction bs with
  | nil => simp [decodeIndex,value]
  | cons b bs ih =>
      constructor
      · change b.toNat+2*(decodeIndex bs).1 = b.toNat+2*value bs
        rw [ih.1]
      · change (decodeIndex bs).2+8 = 8*(bs.length+1)+1
        rw [ih.2]
        omega

/-- Only the operation subtotal changes; physical counters remain unchanged. -/
def charge (q : ℕ) (s : Ledger) : Ledger := {s with operations := s.operations+q}

@[simp] theorem charge_failed (q : ℕ) (s : Ledger) : (charge q s).failed=s.failed := rfl
@[simp] theorem charge_trials (q : ℕ) (s : Ledger) : (charge q s).trials=s.trials := rfl
@[simp] theorem charge_consumed (q : ℕ) (s : Ledger) : (charge q s).consumed=s.consumed := rfl
@[simp] theorem charge_draws (q : ℕ) (s : Ledger) : (charge q s).draws=s.draws := rfl

variable {M : Type → Type} [Monad M]

/-- Same actual draw/update, followed by one paid index conversion. The
dimension occurs only in the type and erased proofs. -/
def drawIndex (bit : M Bool) (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) : M (Fin N × Ledger) := do
  let r ← (trackedDraw bit bound (by omega) fuel).run s
  let d := decodeIndex r.1.index
  pure (⟨d.1,by rw [(decodeIndex_spec _).1,← hb]; exact r.1.index_lt⟩,
    charge (d.2+8) r.2)

/-- Bounds shrink as length(xs), ..., 1. Control reads retained list tails,
never a numerical loop whose length is the potentially large cutoff L. -/
def permutation (bit : M Bool) (fuel : Bits) {A : Type} :
    (xs : List A) → (bound : Bits) → value bound=xs.length →
      Ledger → M (FinitePermutationSampler.Tape xs.length × Ledger)
  | [],_,_,s => pure ((),charge 4 s)
  | _::xs,bound,hb,s => do
      let j ← drawIndex bit fuel bound hb (by simp) s
      let p := BinaryArithmetic.predecessor bound
      let t ← permutation bit fuel xs p.1
        (by rw [(BinaryArithmetic.predecessor_spec bound).1,hb]; simp)
        (charge (p.2+8) j.2)
      pure ((j.1,t.1),charge 8 t.2)

/-- One cutoff-bounded draw per retained active element. -/
def cells (bit : M Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type} :
    (xs : List A) → Ledger → M (FiniteGridSampler.Cells L xs.length × Ledger)
  | [],s => pure ((),charge 4 s)
  | _::xs,s => do
      let j ← drawIndex bit fuel cutoff hcut hL s
      let t ← cells bit fuel cutoff hcut hL xs j.2
      pure ((j.1,t.1),charge 8 t.2)

def tape (bit : M Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type}
    (xs : List A) (bound : Bits) (hb : value bound=xs.length) (s : Ledger) :
    M ((FinitePermutationSampler.Tape xs.length × FiniteGridSampler.Cells L xs.length) × Ledger) := do
  let p ← permutation bit fuel xs bound hb s
  let c ← cells bit fuel cutoff hcut hL xs p.2
  pure ((p.1,c.1),charge 8 c.2)

/-- Erased transport reuses the actual tape constructors. -/
def castTape {m k L : ℕ} (h : m=k)
    (t : FinitePermutationSampler.Tape m × FiniteGridSampler.Cells L m) :
    FinitePermutationSampler.Tape k × FiniteGridSampler.Cells L k := h ▸ t

/-- The dictionary scan is paid here even when materialization later builds
its own active dictionary. The active list and binary count are bound once. -/
def sampleTape (bit : M Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger) :
    M (RetainedTapeInput.Tape L a × Ledger) := do
  let xs := RetainedTapeInput.activeList a
  let c := count xs
  let r ← tape bit fuel cutoff hcut hL xs c.1 (count_spec xs).1
    (charge (EncodedTapeMaterialization.dictionaryBound n+c.2+16) s)
  pure (castTape (RetainedTapeInput.activeList_length a) r.1,charge 8 r.2)

/-- A fresh local operation subtotal is returned once, then added once to
the entering ledger. Physical counters still start at their retained values.
This avoids repeatedly billing earlier callbacks' cumulative operation charge. -/
def callback (bit : M Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) :
    StateT Ledger M (RetainedTapeInput.Tape L a × ℕ) := fun s => do
  let r ← sampleTape bit fuel cutoff hcut hL a {s with operations := 0}
  let increment := r.2.operations+8
  pure ((r.1,increment),{r.2 with operations := s.operations+increment})

section Lawful
variable [LawfulMonad M]

/-- Whole-monad projection preserves the source state and bounded defaults. -/
theorem drawIndex_projection (bit : M Bool) (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) :
    Prod.fst <$> drawIndex bit fuel bound hb hN s =
      MonadicBitSampler.sample (BinaryRandomWord.bitIndex <$> bit) (value fuel) N hN := by
  subst N
  have h := BinaryBoundedSampler.draw_refines bit bound hN fuel
  have hh := congrArg (fun p => (fun r : BitSamplerCoupling.DefaultOutput (value bound) => r.value) <$> p) h
  simpa only [drawIndex,trackedDraw,StateT.run,MonadicBitSampler.sample,
    BinaryBoundedSampler.observe,decodeIndex_spec,Functor.map_map,Function.comp_def,
    bind_pure_comp,bind_map_left,pure_bind] using hh

/-- The ledger never controls either list loop. -/
theorem permutation_projection (bit : M Bool) (fuel : Bits) {A : Type}
    (xs : List A) (bound : Bits) (hb : value bound=xs.length) (s : Ledger) :
    Prod.fst <$> permutation bit fuel xs bound hb s =
      FiniteDrawTrees.execute (MonadicBitSampler.sample
        (BinaryRandomWord.bitIndex <$> bit) (value fuel))
        (RetainedDrawTrees.permutation xs.length) := by
  induction xs generalizing bound s with
  | nil => simp [permutation,RetainedDrawTrees.permutation,FiniteDrawTrees.execute]
  | cons x xs ih =>
      simp only [permutation,List.length_cons,RetainedDrawTrees.permutation,
        MonadicBitSampler.execute_bind,MonadicBitSampler.execute_map,
        MonadicBitSampler.execute_pick,map_bind,bind_pure_comp,Functor.map_map]
      conv_lhs =>
        arg 2
        ext j
        tactic =>
          exact (Functor.map_map Prod.fst (fun t : FinitePermutationSampler.Tape xs.length => (j.1,t)) _).symm.trans
            (congrArg (Functor.map (fun t : FinitePermutationSampler.Tape xs.length => (j.1,t))) (ih _ _ _))
      exact (bind_map_left Prod.fst _ (fun i => Prod.mk i <$> _)).symm.trans
        (congrArg (fun v => v >>= fun i => Prod.mk i <$> _)
          (drawIndex_projection bit fuel bound hb (by simp) s))

theorem cells_projection (bit : M Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type} (xs : List A) (s : Ledger) :
    Prod.fst <$> cells bit fuel cutoff hcut hL xs s =
      FiniteDrawTrees.execute (MonadicBitSampler.sample
        (BinaryRandomWord.bitIndex <$> bit) (value fuel))
        (RetainedDrawTrees.cells L hL xs.length) := by
  induction xs generalizing s with
  | nil => simp [cells,RetainedDrawTrees.cells,FiniteDrawTrees.execute]
  | cons x xs ih =>
      simp only [cells,List.length_cons,RetainedDrawTrees.cells,
        MonadicBitSampler.execute_bind,MonadicBitSampler.execute_map,
        MonadicBitSampler.execute_pick,map_bind,bind_pure_comp,Functor.map_map]
      conv_lhs =>
        arg 2
        ext j
        tactic =>
          exact (Functor.map_map Prod.fst (fun t : FiniteGridSampler.Cells L xs.length => (j.1,t)) _).symm.trans
            (congrArg (Functor.map (fun t : FiniteGridSampler.Cells L xs.length => (j.1,t))) (ih _))
      exact (bind_map_left Prod.fst _ (fun i => Prod.mk i <$> _)).symm.trans
        (congrArg (fun v => v >>= fun i => Prod.mk i <$> _)
          (drawIndex_projection bit fuel cutoff hcut hL s))

theorem tape_projection (bit : M Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type}
    (xs : List A) (bound : Bits) (hb : value bound=xs.length) (s : Ledger) :
    Prod.fst <$> tape bit fuel cutoff hcut hL xs bound hb s =
      FiniteDrawTrees.execute (MonadicBitSampler.sample
        (BinaryRandomWord.bitIndex <$> bit) (value fuel))
        (RetainedDrawTrees.tape L hL xs.length) := by
  simp only [tape,RetainedDrawTrees.tape,MonadicBitSampler.execute_bind,
    MonadicBitSampler.execute_map,map_bind,bind_pure_comp,Functor.map_map]
  conv_lhs =>
    arg 2
    ext p
    tactic =>
      exact (Functor.map_map Prod.fst
        (fun c : FiniteGridSampler.Cells L xs.length => (p.1,c)) _).symm.trans
        (congrArg (Functor.map (fun c : FiniteGridSampler.Cells L xs.length => (p.1,c)))
          (cells_projection bit fuel cutoff hcut hL xs p.2))
  exact (bind_map_left Prod.fst _ (fun i => Prod.mk i <$> _)).symm.trans
    (congrArg (fun v => v >>= fun i => Prod.mk i <$> _)
      (permutation_projection bit fuel xs bound hb s))

/-- Generic typed-tape transport, used only in the refinement proof. -/
theorem execute_tape_cast (sample : (N : ℕ) → 0<N → M (Fin N))
    {m k L : ℕ} (h : m=k) (hL : 0<L) :
    castTape h <$> FiniteDrawTrees.execute sample (RetainedDrawTrees.tape L hL m) =
      FiniteDrawTrees.execute sample (RetainedDrawTrees.tape L hL k) := by
  subst k
  change id <$> _ = _
  exact id_map _

theorem sampleTape_projection (bit : M Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger) :
    Prod.fst <$> sampleTape bit fuel cutoff hcut hL a s =
      FiniteDrawTrees.execute (MonadicBitSampler.sample
        (BinaryRandomWord.bitIndex <$> bit) (value fuel))
        (RetainedDrawTrees.sampleTape hL a) := by
  simp only [sampleTape,bind_pure_comp,Functor.map_map]
  conv_lhs =>
    tactic =>
      exact (Functor.map_map Prod.fst (castTape (RetainedTapeInput.activeList_length a)) _).symm
  rw [tape_projection,execute_tape_cast]
  rfl

/-- Same supplied monad and bit-source suffix as the lowered bounded tree. -/
theorem sampleTape_lower (bit : M Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger) :
    Prod.fst <$> sampleTape bit fuel cutoff hcut hL a s =
      FiniteDrawTrees.execute (MonadicBitSampler.liftBit (BinaryRandomWord.bitIndex <$> bit))
        (LazyFairBitTrees.lower (value fuel) (RetainedDrawTrees.sampleTape hL a)) := by
  rw [MonadicBitSampler.execute_lower_refines,sampleTape_projection]

/-- Resetting only the local cost subtotal does not alter the retained tape
or source-state effects. The actual callback is the same bounded program. -/
theorem callback_projection (bit : M Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger) :
    (fun out => out.1.1) <$> (callback bit fuel cutoff hcut hL a).run s =
      FiniteDrawTrees.execute (MonadicBitSampler.sample
        (BinaryRandomWord.bitIndex <$> bit) (value fuel))
        (RetainedDrawTrees.sampleTape hL a) := by
  simpa only [callback,StateT.run,bind_pure_comp,Functor.map_map,Function.comp_def] using
    sampleTape_projection bit fuel cutoff hcut hL a {s with operations := 0}

end Lawful

noncomputable section

/-- The actual sampler stores at most the supplied bound's bit length in its
returned index. This uses its reached branches, not only the decoded value. -/
theorem draw_index_length (bit : PMF Bool) (bound fuel : Bits)
    (positive : 0<value bound) {r : BinaryBoundedSampler.Output bound}
    (hr : r ∈ (BinaryBoundedSampler.draw bit bound positive fuel).support) :
    r.index.length ≤ bound.length := by
  have aux : ∀ T, ∀ f : Bits, value f=T → ∀ r : BinaryBoundedSampler.Output bound,
      r ∈ (BinaryBoundedSampler.draw bit bound positive f).support →
        r.index.length ≤ bound.length := by
    intro T
    induction T using Nat.strong_induction_on with
    | h T ih =>
      intro f hf r hr
      rw [BinaryBoundedSampler.draw] at hr
      split at hr
      next hzero =>
        have he := (PMF.mem_support_pure_iff _ _).mp hr
        subst r
        exact Nat.zero_le _
      next hzero =>
        have hv : 0<value f := Nat.pos_of_ne_zero
          (fun h => hzero ((isZero_spec f).1.mpr h))
        obtain ⟨x,hx,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
        have hxlen := x.length_eq.le.trans (BinarySamplerCost.width_value_le bound)
        dsimp only at hr
        split at hr
        next accepted =>
          have he := (PMF.mem_support_pure_iff _ _).mp hr
          subst r
          exact hxlen
        next rejected =>
          obtain ⟨tail,htail,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
          have he := (PMF.mem_support_pure_iff _ _).mp hr
          subst r
          have hp := (predecessor_spec f).1
          exact ih (value (predecessor f).1) (by rw [hp,← hf]; omega)
            (predecessor f).1 rfl tail htail
  exact aux (value fuel) fuel rfl r hr

/-- Exact same-call support, including literal index conversion and ledger. -/
theorem drawIndex_support (bit : PMF Bool) (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) {out : Fin N × Ledger}
    (hout : out ∈ (drawIndex bit fuel bound hb hN s).support) :
    ∃ r : BinaryBoundedSampler.Output bound,
      r ∈ (BinaryBoundedSampler.draw bit bound (by omega) fuel).support ∧
      out.1.val=value r.index ∧
      out.2=charge ((decodeIndex r.index).2+8) (record s r) := by
  rw [drawIndex] at hout
  obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have h := trackedDraw_support bit bound fuel (by omega) s hr
  exact ⟨r.1,h.1,(decodeIndex_spec _).1,by rw [h.2]⟩

theorem drawIndex_metadata (bit : PMF Bool) (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) {out : Fin N × Ledger}
    (hout : out ∈ (drawIndex bit fuel bound hb hN s).support) :
    value out.2.draws=value s.draws+1 ∧ s.operations ≤ out.2.operations := by
  obtain ⟨r,hr,hi,he⟩ := drawIndex_support bit fuel bound hb hN s hout
  rw [he,charge_draws,record_draws]
  refine ⟨rfl,?_⟩
  dsimp only [charge,record]
  omega

/-- Includes actual bounded sampling, physical counter updates and decoding. -/
theorem drawIndex_charge (bit : PMF Bool) (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) {out : Fin N × Ledger}
    (hout : out ∈ (drawIndex bit fuel bound hb hN s).support) :
    out.2.operations ≤ s.operations+updateBound s bound fuel+8*bound.length+9 := by
  obtain ⟨r,hr,hi,he⟩ := drawIndex_support bit fuel bound hb hN s hout
  have hq := record_draw_charge bit bound fuel (by omega) s hr
  have hl := draw_index_length bit bound fuel (by omega) hr
  rw [he]
  dsimp only [charge]
  rw [(decodeIndex_spec _).2]
  omega

/-- Actual stored counter length, including any padding on the entering
ledger. This supplies the local invariant needed for a summed tape budget. -/
def ledgerWidth (s : Ledger) : ℕ :=
  max s.trials.length (max s.consumed.length s.draws.length)

theorem drawIndex_width (bit : PMF Bool) (fuel bound : Bits) {N : ℕ}
    (hb : value bound=N) (hN : 0<N) (s : Ledger) {out : Fin N × Ledger}
    (hout : out ∈ (drawIndex bit fuel bound hb hN s).support) :
    ledgerWidth out.2 ≤ ledgerWidth s+value fuel+bound.length+2 := by
  obtain ⟨r,hr,hi,he⟩ := drawIndex_support bit fuel bound hb hN s hout
  have h := record_lengths s r
  have hb' := BinarySamplerCost.draw_bounded bit bound fuel (by omega) hr
  rw [he]
  simp only [ledgerWidth,charge_trials,charge_consumed,charge_draws]
  unfold BinarySamplerCost.Bounded at hb'
  omega

theorem permutation_draws (bit : PMF Bool) (fuel : Bits) {A : Type}
    (xs : List A) (bound : Bits) (hb : value bound=xs.length) (s : Ledger)
    {out : FinitePermutationSampler.Tape xs.length × Ledger}
    (hout : out ∈ (permutation bit fuel xs bound hb s).support) :
    value out.2.draws=value s.draws+xs.length := by
  induction xs generalizing bound s with
  | nil =>
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      simp [charge]
  | cons x xs ih =>
      rw [permutation] at hout
      obtain ⟨j,hj,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨t,ht,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      have hfirst := (drawIndex_metadata bit fuel bound hb (by simp) s hj).1
      have htail := ih _ _ _ ht
      simp only [charge_draws,List.length_cons] at htail ⊢
      omega

theorem cells_draws (bit : PMF Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type} (xs : List A) (s : Ledger)
    {out : FiniteGridSampler.Cells L xs.length × Ledger}
    (hout : out ∈ (cells bit fuel cutoff hcut hL xs s).support) :
    value out.2.draws=value s.draws+xs.length := by
  induction xs generalizing s with
  | nil =>
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      simp [charge]
  | cons x xs ih =>
      rw [cells] at hout
      obtain ⟨j,hj,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      obtain ⟨t,ht,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
      have he := (PMF.mem_support_pure_iff _ _).mp hout
      subst out
      have hfirst := (drawIndex_metadata bit fuel cutoff hcut hL s hj).1
      have htail := ih _ ht
      simp only [charge_draws,List.length_cons]
      omega

theorem tape_draws (bit : PMF Bool) (fuel cutoff : Bits) {L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) {A : Type}
    (xs : List A) (bound : Bits) (hb : value bound=xs.length) (s : Ledger)
    {out : (FinitePermutationSampler.Tape xs.length × FiniteGridSampler.Cells L xs.length) × Ledger}
    (hout : out ∈ (tape bit fuel cutoff hcut hL xs bound hb s).support) :
    value out.2.draws=value s.draws+2*xs.length := by
  rw [tape] at hout
  obtain ⟨p,hp,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨c,hc,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have hp' := permutation_draws bit fuel xs bound hb s hp
  have hc' := cells_draws bit fuel cutoff hcut hL xs p.2 hc
  simp only [charge_draws]
  omega

/-- Exactly two draws for each literal retained active label, even when fuel
is zero or some rejection trial exhausts. No successful-sampling premise. -/
theorem sampleTape_draws (bit : PMF Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger)
    {out : RetainedTapeInput.Tape L a × Ledger}
    (hout : out ∈ (sampleTape bit fuel cutoff hcut hL a s).support) :
    value out.2.draws=value s.draws+2*Fintype.card ↥(remainingSet a) := by
  rw [sampleTape] at hout
  obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  have h := tape_draws bit fuel cutoff hcut hL (RetainedTapeInput.activeList a)
    (count (RetainedTapeInput.activeList a)).1 (count_spec _).1 _ hr
  simpa only [charge_draws,RetainedTapeInput.activeList_length] using h

/-- One increment is returned, and exactly that increment is accumulated.
Sequential uses therefore telescope without rebilling cumulative history. -/
theorem callback_increment (bit : PMF Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger)
    {out : (RetainedTapeInput.Tape L a × ℕ) × Ledger}
    (hout : out ∈ ((callback bit fuel cutoff hcut hL a).run s).support) :
    out.2.operations=s.operations+out.1.2 ∧
      value out.2.draws=value s.draws+2*Fintype.card ↥(remainingSet a) := by
  change out ∈ (sampleTape bit fuel cutoff hcut hL a {s with operations := 0} >>= _).support at hout
  obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  have he := (PMF.mem_support_pure_iff _ _).mp hout
  subst out
  exact ⟨rfl,sampleTape_draws bit fuel cutoff hcut hL a {s with operations := 0} hr⟩

theorem callback_draw_bound (bit : PMF Bool) (fuel cutoff : Bits) {n L : ℕ}
    (hcut : value cutoff=L) (hL : 0<L) (a : PairFlags n) (s : Ledger)
    {out : (RetainedTapeInput.Tape L a × ℕ) × Ledger}
    (hout : out ∈ ((callback bit fuel cutoff hcut hL a).run s).support) :
    value out.2.draws ≤ value s.draws+2*n*n := by
  rw [(callback_increment bit fuel cutoff hcut hL a s hout).2]
  simpa only [Nat.mul_assoc] using Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 (RetainedDrawTrees.active_card_le a)) (value s.draws)

end

/-- The exact identified tree has at most two finite draws per active label. -/
theorem sampleTape_draw_budget {n L : ℕ} (hL : 0<L) (a : PairFlags n) :
    FiniteDrawTrees.Within (2*n*n) (RetainedDrawTrees.sampleTape hL a) :=
  RetainedDrawTrees.sampleTape_within hL a

/-- Existing adaptive bound for the next controller composition. This does
not assert a whole controller/metadata refinement from one-tape refinement. -/
theorem controller_draw_budget {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
    {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
    {H : ∃ P, selector P} (Q : RetainedGridState.Optimizer H) (hL : 0<L)
    (C : RetainedGridState.CutOracle G L hL) (R restarts epochs : ℕ)
    (s : RetainedGridState.Code G D L) :
    FiniteDrawTrees.Within (epochs*(2*n*n))
      (RetainedDrawTrees.runTree Q hL C R restarts epochs s) :=
  RetainedDrawTrees.runTree_within Q hL C R restarts epochs s

end DirectedFlowCutGap.BinaryRetainedTape
