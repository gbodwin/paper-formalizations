import DirectedFlowCutGap.BinaryWeightedMasses
import DirectedFlowCutGap.BinarySamplerCost
import DirectedFlowCutGap.BinaryFractionalCore

/-!
# Stored binary totals and weighted ticket selection

Preparation computes the integer masses once and adds their actual bit words.
The sampler consumes the retained total, calls the checked bounded-bit routine
once, and selects with the returned ticket. Its failure flag and both binary
counters are retained. Zero total is a distinct explicit result.

Labels are complete Boolean lists, not their numerical denotations. In the
event adapter the label is the actual retained column mask, so there is no
index dictionary or unpriced selected-event lookup. Array-to-list conversion
and label copying are charged. Retained Fraction fields are borrowed; their
binary arithmetic is paid by the mass constructor. Natural charges are ghost
instrumentation in the agreed structural Boolean/list model.

The bounded sampler is biased on exhaustion. This module gives program,
support and cost refinement, not an exact-uniform or adaptive error theorem.
-/
namespace DirectedFlowCutGap.BinaryWeightedSampling
open BinaryArithmetic BinaryWeightedMasses

/-- Equality of full label bytes, including zero padding. -/
theorem choose_exact_labels (xs : MassList) (ticket : Bits) :
    (BinaryWeightedChoice.choose xs ticket).1 =
      IntegerWeightedChoice.choose (data xs) (value ticket) := by
  induction xs generalizing ticket with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨label,mass⟩
      have hc := (compare_spec ticket mass).1
      have hs := (BinaryDivision.sub_spec ticket mass).1
      cases hb : (BinaryArithmetic.compare ticket mass).less
      · have hn : ¬ value ticket < value mass := by simpa [hb] using hc
        simpa [BinaryWeightedChoice.choose,data,hb,IntegerWeightedChoice.choose,hn,hs]
          using ih (BinaryDivision.sub ticket mass).1
      · have hl : value ticket < value mass := hc.mp hb
        simp [BinaryWeightedChoice.choose,data,hb,IntegerWeightedChoice.choose,hl,
          (BinaryWeightedChoice.copyBits_spec label).1]

/-- Literal binary addition of every retained integer mass. -/
def sumMass : MassList → Bits × ℕ
  | [] => ([],1)
  | (_,mass)::xs =>
      let tail := sumMass xs
      let total := addCanonical mass tail.1
      (total.1,tail.2+total.2+8)

theorem sumMass_value (xs : MassList) :
    value (sumMass xs).1 = IntegerWeightedChoice.total (data xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨label,mass⟩
      simp [sumMass,(canonical_values mass (sumMass xs).1).1,ih,
        IntegerWeightedChoice.total,data]

theorem addCanonical_length (a b : Bits) :
    (addCanonical a b).1.length ≤ max a.length b.length+1 := by
  exact ((trim_spec (add false a b).1).2.2.1).trans (add_spec false a b).2.1

/-- A coarse structural width bound avoids assuming canonical input words. -/
theorem sumMass_length (xs : MassList) (B : ℕ)
    (h : ∀ x ∈ xs, x.2.length ≤ B) :
    (sumMass xs).1.length ≤ B+xs.length := by
  induction xs with
  | nil => simp [sumMass]
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      have hs := addCanonical_length x.2 (sumMass xs).1
      simp only [sumMass,List.length_cons]
      omega

def sumBound (k B : ℕ) : ℕ := k*(32*(B+k+2)+8)+1

theorem sumMass_cost (xs : MassList) (B : ℕ)
    (h : ∀ x ∈ xs, x.2.length ≤ B) : (sumMass xs).2 ≤ sumBound xs.length B := by
  induction xs with
  | nil => simp [sumMass,sumBound]
  | cons x xs ih =>
      have hx := h x List.mem_cons_self
      have hh := fun y hy => h y (List.mem_cons_of_mem x hy)
      have ht := sumMass_length xs B hh
      have hc := (canonical_charges (hx.trans (Nat.le_add_right B xs.length)) ht).1
      have hi := ih hh
      simp only [sumMass,List.length_cons]
      unfold sumBound at hi ⊢
      nlinarith

structure Prepared where
  denominator : Bits
  masses : MassList
  total : Bits
  operations : ℕ
  total_eq : value total = IntegerWeightedChoice.total (data masses)

def prepare (xs : Input) : Prepared :=
  let encoded := encode xs
  let total := sumMass encoded.masses
  ⟨encoded.denominator,encoded.masses,total.1,
    encoded.operations+total.2+8,sumMass_value encoded.masses⟩

def preparationBound (k B C : ℕ) : ℕ :=
  k*(k+3)*costUnit k B C+1+sumBound k (k*B+1)+8

theorem prepare_widths (xs : Input) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ BinaryRational.StoredBounded x.2 B) :
    (prepare xs).total.length ≤ xs.length*(B+1)+1 ∧
      ∀ x ∈ (prepare xs).masses, x.1.length ≤ C ∧ x.2.length ≤ xs.length*B+1 := by
  have hm := encode_stored xs B (fun x hx => (h x hx).2)
  have hl := encode_label_bound xs C (fun x hx => (h x hx).1)
  have ht := sumMass_length (encode xs).masses (xs.length*B+1) hm.2
  rw [encode_length] at ht
  refine ⟨?_,fun x hx => ⟨hl x hx,hm.2 x hx⟩⟩
  change (sumMass (encode xs).masses).1.length ≤ _
  nlinarith

theorem prepare_cost (xs : Input) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ BinaryRational.StoredBounded x.2 B) :
    (prepare xs).operations ≤ preparationBound xs.length B C := by
  have he := encode_cost xs B C h
  have hw := encode_stored xs B (fun x hx => (h x hx).2)
  have hs := sumMass_cost (encode xs).masses (xs.length*B+1) hw.2
  rw [encode_length] at hs
  dsimp only [prepare,preparationBound]
  omega

/-- A legal ticket selects an actual positive-mass entry, preserving its bytes. -/
theorem choose_member (p : Prepared) (ticket : Bits) (ht : value ticket < value p.total) :
    ∃ label mass, (BinaryWeightedChoice.choose p.masses ticket).1 = some label ∧
      (label,mass) ∈ p.masses ∧ 0 < value mass := by
  rw [p.total_eq] at ht
  obtain ⟨label,w,he,hm,hp⟩ := IntegerWeightedChoice.choose_some ht
  obtain ⟨x,hx,hxw⟩ := List.mem_map.mp hm
  rcases x with ⟨a,mass⟩
  have ha : a=label := congrArg Prod.fst hxw
  have hw : value mass=w := congrArg Prod.snd hxw
  subst a
  refine ⟨label,mass,?_,hx,by simpa [hw] using hp⟩
  rw [choose_exact_labels]
  exact he

structure Result where
  label : Option Bits
  zeroTotal : Bool
  failed : Bool
  trials : Bits
  consumed : Bits
  operations : ℕ

/-- No additional random request occurs in the continuation. -/
def finish (p : Prepared) (r : Option (BinaryBoundedSampler.Output p.total) × ℕ) : Result :=
  match r.1 with
  | none => ⟨none,true,true,[],[],r.2+4⟩
  | some ticket =>
      let selected := BinaryWeightedChoice.choose p.masses ticket.index
      ⟨selected.1,false,ticket.failed,ticket.trials,ticket.consumed,r.2+selected.2+8⟩

def samplePrepared {m : Type → Type} [Monad m] (bit : m Bool)
    (p : Prepared) (fuel : Bits) : m Result :=
  finish p <$> BinaryBoundedSampler.checkedDrawCharged bit p.total fuel

def sample {m : Type → Type} [Monad m] (bit : m Bool) (xs : Input) (fuel : Bits) : m Result :=
  let p := prepare xs
  (fun r => {r with operations := p.operations+r.operations+4}) <$> samplePrepared bit p fuel

theorem finish_counters (p : Prepared) (ticket : BinaryBoundedSampler.Output p.total) (q : ℕ) :
    (finish p (some ticket,q)).failed = ticket.failed ∧
    (finish p (some ticket,q)).trials = ticket.trials ∧
    (finish p (some ticket,q)).consumed = ticket.consumed := by
  exact ⟨rfl,rfl,rfl⟩

theorem finish_member (p : Prepared) (ticket : BinaryBoundedSampler.Output p.total) (q : ℕ) :
    ∃ label mass, (finish p (some ticket,q)).label = some label ∧
      (label,mass) ∈ p.masses ∧ 0 < value mass :=
  choose_member p ticket.index ticket.index_lt

/-- The exact byte-label observation is an equality in the entire supplied monad. -/
theorem samplePrepared_label {m : Type → Type} [Monad m] [LawfulMonad m]
    (bit : m Bool) (p : Prepared) (fuel : Bits) :
    (fun r => r.label) <$> samplePrepared bit p fuel =
      (fun r : Option (BinaryBoundedSampler.Output p.total) × ℕ =>
        match r.1 with
        | none => none
        | some ticket => IntegerWeightedChoice.choose (data p.masses) (value ticket.index)) <$>
        BinaryBoundedSampler.checkedDrawCharged bit p.total fuel := by
  simp only [samplePrepared,Functor.map_map]
  congr 1
  funext r
  rcases r with ⟨r,q⟩
  cases r with
  | none => rfl
  | some r => exact choose_exact_labels p.masses r.index

/-- This observation is proof-side only; execution retains the binary counters. -/
def observe (r : Result) : Option Bits × Bool × Bool × ℕ × ℕ :=
  (r.label,r.zeroTotal,r.failed,value r.trials,value r.consumed)

theorem samplePrepared_observe {m : Type → Type} [Monad m] [LawfulMonad m]
    (bit : m Bool) (p : Prepared) (fuel : Bits) :
    observe <$> samplePrepared bit p fuel =
      (fun r : Option (BinaryBoundedSampler.Output p.total) × ℕ =>
        match r.1 with
        | none => (none,true,true,0,0)
        | some ticket =>
            (IntegerWeightedChoice.choose (data p.masses) (value ticket.index),
              false,ticket.failed,value ticket.trials,value ticket.consumed)) <$>
        BinaryBoundedSampler.checkedDrawCharged bit p.total fuel := by
  simp only [samplePrepared,Functor.map_map]
  congr 1
  funext r
  rcases r with ⟨r,q⟩
  cases r with
  | none => rfl
  | some r => simp only [observe,finish,choose_exact_labels]

noncomputable section

/-- The sampler's existing cost record did not include its index-word length. -/
theorem draw_index_length (bit : PMF Bool) (bound fuel : Bits) (positive : 0<value bound)
    {r : BinaryBoundedSampler.Output bound}
    (hr : r ∈ (BinaryBoundedSampler.draw bit bound positive fuel).support) :
    r.index.length ≤ bound.length := by
  have aux : ∀ T, ∀ f : Bits, value f=T → ∀ r : BinaryBoundedSampler.Output bound,
      r ∈ (BinaryBoundedSampler.draw bit bound positive f).support → r.index.length ≤ bound.length := by
    intro T
    induction T using Nat.strong_induction_on with
    | h T ih =>
      intro f hf r hr
      have hz := isZero_spec f
      rw [BinaryBoundedSampler.draw] at hr
      split at hr
      next hzero =>
        have he := (PMF.mem_support_pure_iff _ _).mp hr
        subst r
        exact Nat.zero_le _
      next hzero =>
        have hv : 0<value f := Nat.pos_of_ne_zero (fun h => hzero (hz.1.mpr h))
        obtain ⟨x,_hx,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
        dsimp only at hr
        split at hr
        next accepted =>
          have he := (PMF.mem_support_pure_iff _ _).mp hr
          subst r
          exact x.length_eq.le.trans (BinarySamplerCost.width_value_le bound)
        next rejected =>
          obtain ⟨tail,htail,hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
          have he := (PMF.mem_support_pure_iff _ _).mp hr
          subst r
          have hp := BinaryArithmetic.predecessor_spec f
          exact ih (value (BinaryArithmetic.predecessor f).1) (by rw [hp.1,← hf];omega)
            (BinaryArithmetic.predecessor f).1 rfl tail htail
  exact aux (value fuel) fuel rfl r hr

theorem checked_index_length (bit : PMF Bool) (bound fuel : Bits)
    {out : Option (BinaryBoundedSampler.Output bound) × ℕ}
    (hout : out ∈ (BinaryBoundedSampler.checkedDrawCharged bit bound fuel).support) :
    ∀ r, out.1=some r → r.index.length ≤ bound.length := by
  rw [BinaryBoundedSampler.checkedDrawCharged] at hout
  split at hout
  next hzero =>
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    intro r hr
    cases hr
  next hpositive =>
    obtain ⟨r,hr,hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
    have he := (PMF.mem_support_pure_iff _ _).mp hout
    subst out
    intro s hs
    cases hs
    exact draw_index_length bit bound fuel _ hr

def sampleBound (p : Prepared) (fuel : Bits) (B C : ℕ) : ℕ :=
  BinarySamplerCost.checkedInstructionBound p.total fuel+
    p.masses.length*(160*(max p.total.length B+1)+4*C+16)+9

theorem samplePrepared_cost (bit : PMF Bool) (p : Prepared) (fuel : Bits) (B C : ℕ)
    (h : ∀ x ∈ p.masses, x.1.length ≤ C ∧ x.2.length ≤ B)
    {out : Result} (hout : out ∈ (samplePrepared bit p fuel).support) :
    out.operations ≤ sampleBound p fuel B C := by
  obtain ⟨r,hr,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have hc := (BinarySamplerCost.checked_draw_bounded bit p.total fuel hr).1
  have hi := checked_index_length bit p.total fuel hr
  rcases r with ⟨r,q⟩
  cases r with
  | none =>
      dsimp only [finish,sampleBound]
      omega
  | some ticket =>
      have ht := (hi ticket rfl).trans (Nat.le_max_left p.total.length B)
      have hx : ∀ x ∈ p.masses, x.1.length ≤ C ∧ x.2.length ≤ max p.total.length B :=
        fun x hx => ⟨(h x hx).1,(h x hx).2.trans (Nat.le_max_right p.total.length B)⟩
      have hs := BinaryWeightedChoice.choose_bound p.masses ticket.index _ C ht hx
      dsimp only [finish,sampleBound]
      omega

theorem sample_cost (bit : PMF Bool) (xs : Input) (fuel : Bits) (B C : ℕ)
    (h : ∀ x ∈ xs, x.1.length ≤ C ∧ BinaryRational.StoredBounded x.2 B)
    {out : Result} (hout : out ∈ (sample bit xs fuel).support) :
    out.operations ≤ preparationBound xs.length B C+
      sampleBound (prepare xs) fuel (xs.length*B+1) C+4 := by
  obtain ⟨r,hr,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have hp := prepare_cost xs B C h
  have hs := samplePrepared_cost bit (prepare xs) fuel (xs.length*B+1) C
    (prepare_widths xs B C h).2 hr
  dsimp only
  omega

end

/-- The only payload conversion reads the retained event mask and copies it.
The amount's two bit-word fields remain borrowed references. -/
def eventInput {m : ℕ} : List (BinaryFractionalCore.Event m) → Input × ℕ
  | [] => ([],1)
  | e::es =>
      let tail := eventInput es
      let copied := BinaryWeightedChoice.copyBits e.choice.mask.toList
      ((copied.1,e.amount)::tail.1,tail.2+copied.2+2*m+12)

theorem eventInput_value {m : ℕ} (es : List (BinaryFractionalCore.Event m)) :
    (eventInput es).1 = es.map (fun e => (e.choice.mask.toList,e.amount)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [eventInput,ih,(BinaryWeightedChoice.copyBits_spec e.choice.mask.toList).1]

theorem eventInput_cost {m : ℕ} (es : List (BinaryFractionalCore.Event m)) :
    (eventInput es).2 ≤ es.length*(6*m+13)+1 := by
  induction es with
  | nil => simp [eventInput]
  | cons e es ih =>
      have hc := (BinaryWeightedChoice.copyBits_spec e.choice.mask.toList).2
      simp only [Vector.length_toList] at hc
      simp only [eventInput,List.length_cons]
      nlinarith

/-- A selected payload is exactly one retained event's mask, with its full
resource dimension. No numerical label decoder is used in this correspondence. -/
theorem prepared_event_label {m : ℕ} (es : List (BinaryFractionalCore.Event m))
    {label mass : Bits} (h : (label,mass) ∈ (prepare (eventInput es).1).masses) :
    ∃ e ∈ es, label=e.choice.mask.toList ∧ label.length=m := by
  have hl : label ∈ (encode (eventInput es).1).masses.map Prod.fst :=
    List.mem_map.mpr ⟨(label,mass),h,rfl⟩
  rw [encode_labels,eventInput_value,List.map_map] at hl
  obtain ⟨e,he,hel⟩ := List.mem_map.mp hl
  refine ⟨e,he,hel.symm,?_⟩
  rw [← hel]
  simp

theorem finish_event {m : ℕ} (es : List (BinaryFractionalCore.Event m))
    (ticket : BinaryBoundedSampler.Output (prepare (eventInput es).1).total) (q : ℕ) :
    ∃ e ∈ es, (finish (prepare (eventInput es).1) (some ticket,q)).label =
      some e.choice.mask.toList ∧ e.choice.mask.toList.length=m := by
  obtain ⟨label,mass,hl,hm,_hp⟩ := finish_member (prepare (eventInput es).1) ticket q
  obtain ⟨e,he,heq,_hlen⟩ := prepared_event_label es hm
  exact ⟨e,he,by simpa [heq] using hl,by simp⟩

/-- The full entry executes event conversion, mass preparation and one draw
once each, and keeps their independently charged totals. -/
def sampleEvents {m : ℕ} {M : Type → Type} [Monad M] (bit : M Bool)
    (es : List (BinaryFractionalCore.Event m)) (fuel : Bits) : M Result :=
  let input := eventInput es
  (fun r => {r with operations := input.2+r.operations+4}) <$> sample bit input.1 fuel

noncomputable section

theorem sampleEvents_cost {m : ℕ} (bit : PMF Bool)
    (es : List (BinaryFractionalCore.Event m)) (fuel : Bits) (B : ℕ)
    (h : ∀ e ∈ es, BinaryRational.StoredBounded e.amount B)
    {out : Result} (hout : out ∈ (sampleEvents bit es fuel).support) :
    out.operations ≤ es.length*(6*m+13)+1+preparationBound es.length B m+
      sampleBound (prepare (eventInput es).1) fuel (es.length*B+1) m+8 := by
  have hi : ∀ x ∈ (eventInput es).1,
      x.1.length ≤ m ∧ BinaryRational.StoredBounded x.2 B := by
    rw [eventInput_value]
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact ⟨by simp,h e he⟩
  have hlen : (eventInput es).1.length=es.length := by simp [eventInput_value]
  obtain ⟨r,hr,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  have hs := sample_cost bit (eventInput es).1 fuel B m hi hr
  rw [hlen] at hs
  have hc := eventInput_cost es
  dsimp only
  omega

end

end DirectedFlowCutGap.BinaryWeightedSampling
