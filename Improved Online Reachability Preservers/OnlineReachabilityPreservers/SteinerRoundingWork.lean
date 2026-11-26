import Mathlib.Data.Nat.BinaryRec
import OnlineReachabilityPreservers.SteinerEarlyRound
import OnlineReachabilityPreservers.SteinerWeightedChargeWork

/-! Count weight lookups in finite rounding trials, including ancestor minima and threshold tests. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {height : ℕ}

private def rowWithWork {I A : Type*} (f : I → A × ℕ) : I ↪ I × (A × ℕ) :=
  ⟨fun v => (v,f v),fun _ _ equal => congrArg Prod.fst equal⟩

private theorem rowWork_le {I A : Type*} (s : Finset I) (f : I → A × ℕ) (B : ℕ)
    (each : ∀ x ∈ s, (f x).2 ≤ B) :
    (∑ r ∈ s.map (rowWithWork f), r.2.2) ≤ s.card*B := by
  rw [sum_map]
  calc
    _ ≤ ∑ _ ∈ s, B := sum_le_sum each
    _ = _ := by simp

private def rootCappedCapacityWithWork (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  if v = heightRoot then (2^tier,0)
  else
    let amount := units v
    (min (2^tier) (dyadicCapacity amount.1),amount.2)

omit [Fintype V] in
private theorem rootCappedCapacityWithWork_spec (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (cap : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := rootCappedCapacityWithWork tier units v
    out.1 = rootCappedCapacity tier (fun a => (units a).1) v ∧ out.2 ≤ B := by
  by_cases root : v = heightRoot
  · simp [rootCappedCapacityWithWork,rootCappedCapacity,root]
  · simpa [rootCappedCapacityWithWork,rootCappedCapacity,root] using cap v

@[inline] private def historyCapacityUsingWithWork (cap : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  let source := historyAncestors v
  let row := rowWithWork cap
  let results := source.map row
  have present : v ∈ source := mem_historyAncestors.mpr List.prefix_rfl
  (results.inf' ⟨row v,mem_map_of_mem _ present⟩ (fun e => e.2.1),∑ e ∈ results, e.2.2)

private theorem historyCapacityUsingWithWork_spec (cap : HeightNode V height → ℕ × ℕ)
    (tier : ℕ) (units : HeightNode V height → ℕ) (B : ℕ)
    (rowSpec : ∀ a, (cap a).1 = rootCappedCapacity tier units a ∧ (cap a).2 ≤ B)
    (v : HeightNode V height) :
    let out := historyCapacityUsingWithWork cap v
    out.1 = historyCapacityUnits tier units v ∧ out.2 ≤ (height+1)*B := by
  let source := historyAncestors v
  let row := rowWithWork cap
  let values := source.map row
  have exact : (historyCapacityUsingWithWork cap v).1 = historyCapacityUnits tier units v := by
    have fixed : source.Nonempty := ⟨v,mem_historyAncestors.mpr List.prefix_rfl⟩
    have mapped : values.Nonempty := fixed.map
    let read (r : HeightNode V height × (ℕ × ℕ)) := r.2.1
    change values.inf' mapped read = source.inf' fixed (rootCappedCapacity tier units)
    calc
      _ = source.inf' fixed (read ∘ row) := Finset.inf'_map read mapped
      _ = _ := congrArg (source.inf' fixed) (funext fun a => (rowSpec a).1)
  refine ⟨exact,?_⟩
  exact (rowWork_le source cap B (fun a _ => (rowSpec a).2)).trans
    (Nat.mul_le_mul_right B (historyAncestors_card_le v))

/-- Compute the ancestor minimum from one cached row per ancestor. -/
def historyCapacityWithWork (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  historyCapacityUsingWithWork (rootCappedCapacityWithWork tier units) v

theorem historyCapacityWithWork_spec (tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := historyCapacityWithWork tier units v
    out.1 = historyCapacityUnits tier (fun a => (units a).1) v ∧
      out.2 ≤ (height+1)*B :=
  historyCapacityUsingWithWork_spec _ tier (fun a => (units a).1) B
    (rootCappedCapacityWithWork_spec tier units B bound) v

/-- The two ancestor minima are evaluated once each. -/
def historyCutoffWithWork (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  if v = heightRoot then (2^sampleTier,0)
  else
    let top := historyCapacityWithWork tier units v
    let bottom := historyCapacityWithWork tier units (heightParent v)
    (2^sampleTier * top.1 / bottom.1,top.2+bottom.2)

theorem historyCutoffWithWork_spec (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := historyCutoffWithWork sampleTier tier units v
    out.1 = historyCutoff sampleTier tier (fun a => (units a).1) v ∧
      out.2 ≤ 2*(height+1)*B := by
  by_cases root : v = heightRoot
  · simp [historyCutoffWithWork,historyCutoff,root]
  · obtain ⟨top,up⟩ := historyCapacityWithWork_spec tier units B bound v
    obtain ⟨bottom,down⟩ := historyCapacityWithWork_spec tier units B bound (heightParent v)
    simp only [historyCutoffWithWork,historyCutoff,root,ite_false,top,bottom,true_and]
    exact (Nat.add_le_add up down).trans_eq (by ring)

/-- Round up to a strict dyadic capacity with a tier cap. Halving stops
when the cap is reached, so the loop length is bounded by the tier. -/
def cappedDyadicCapacityWithWordWork : ℕ → ℕ → ℕ × ℕ
  | 0, units => if units = 0 then (0,4) else (1,4)
  | tier+1, units =>
    if units = 0 then (0,4) else if units = 1 then (2,6) else
      let smaller := cappedDyadicCapacityWithWordWork tier (units / 2)
      (smaller.1+smaller.1,smaller.2+8)

theorem cappedDyadicCapacityWithWordWork_spec (tier units : ℕ) :
    let out := cappedDyadicCapacityWithWordWork tier units
    out.1 = min (2^tier) (dyadicCapacity units) ∧ out.2 ≤ 8*(tier+1)+3 := by
  induction tier generalizing units with
  | zero =>
    by_cases zero : units = 0
    · simp [zero,cappedDyadicCapacityWithWordWork,dyadicCapacity]
    · have positive : 1 ≤ dyadicCapacity units := (Nat.pos_of_ne_zero zero).trans_le (dyadicCapacity_bounds units).1
      simp [zero,cappedDyadicCapacityWithWordWork,min_eq_left positive]
  | succ tier ih =>
    by_cases zero : units = 0
    · simp [zero,cappedDyadicCapacityWithWordWork,dyadicCapacity]
      omega
    by_cases one : units = 1
    · subst units
      have bound : 2 ≤ (2:ℕ)^(tier+1) := by
        simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 1 ≤ tier+1 by omega)
      have value : dyadicCapacity 1 = 2 := by decide
      simp only [cappedDyadicCapacityWithWordWork,show (1:ℕ) ≠ 0 by decide,ite_false,ite_true,value,min_eq_right bound,true_and]
      omega
    have halfPositive : units / 2 ≠ 0 := by omega
    have shiftPositive : units >>> 1 ≠ 0 := by simpa only [Nat.shiftRight_one] using halfPositive
    have binary := Nat.log2_eq_succ_log2_shiftRight shiftPositive
    rw [Nat.shiftRight_one] at binary
    obtain ⟨value,work⟩ := ih (units / 2)
    simp only [cappedDyadicCapacityWithWordWork,zero,one,ite_false]
    refine ⟨?_,by omega⟩
    simp only [value,dyadicCapacity,ite_eq_right zero,ite_eq_right halfPositive]
    rw [show units.log2+1 = (units/2).log2+1+1 from by omega,
      pow_succ (2:ℕ) tier,pow_succ (2:ℕ) ((units/2).log2+1),Nat.mul_min_mul_right,Nat.mul_two]

private def rootCappedCapacityFromPowerWithWordWork (tier power : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (v : HeightNode V height) : ℕ × ℕ :=
  if v = heightRoot then (power,9) else
    let amount := units v
    let rounded := cappedDyadicCapacityWithWordWork tier amount.1
    (rounded.1,amount.2+rounded.2+14)

omit [Fintype V] in
private theorem rootCappedCapacityFromPowerWithWordWork_spec (tier power : ℕ) (exactPower : power = 2^tier)
    (units : HeightNode V height → ℕ × ℕ) (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := rootCappedCapacityFromPowerWithWordWork tier power units v
    out.1 = rootCappedCapacity tier (fun a => (units a).1) v ∧ out.2 ≤ B+8*(tier+1)+17 := by
  by_cases root : v = heightRoot
  · simp only [rootCappedCapacityFromPowerWithWordWork,rootCappedCapacity,root,ite_true,exactPower,true_and]
    omega
  · obtain ⟨value,work⟩ := cappedDyadicCapacityWithWordWork_spec tier (units v).1
    simp only [rootCappedCapacityFromPowerWithWordWork,rootCappedCapacity,root,ite_false,value,true_and]
    have read := bound v
    omega

/-- Compute one ancestor cutoff given the two powers used throughout a
rounding tier. Meter the arithmetic and the supplied capacity reads. -/
def historyCutoffFromPowersWithWordWork (samplePower tierPower tier : ℕ)
    (units : HeightNode V height → ℕ × ℕ) (v : HeightNode V height) : ℕ × ℕ :=
  if v = heightRoot then (samplePower,4) else
    let cap := rootCappedCapacityFromPowerWithWordWork tier tierPower units
    let top := historyCapacityUsingWithWork cap v
    let bottom := historyCapacityUsingWithWork cap (heightParent v)
    (samplePower*top.1/bottom.1,top.2+bottom.2+8)

theorem historyCutoffFromPowersWithWordWork_spec (sampleTier tier samplePower tierPower : ℕ)
    (sampleExact : samplePower = 2^sampleTier) (tierExact : tierPower = 2^tier)
    (units : HeightNode V height → ℕ × ℕ) (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := historyCutoffFromPowersWithWordWork samplePower tierPower tier units v
    out.1 = historyCutoff sampleTier tier (fun a => (units a).1) v ∧
      out.2 ≤ 2*(height+1)*(B+8*(tier+1)+17)+8 := by
  by_cases root : v = heightRoot
  · simp [historyCutoffFromPowersWithWordWork,historyCutoff,root,sampleExact]
  let cap := rootCappedCapacityFromPowerWithWordWork tier tierPower units
  have read := rootCappedCapacityFromPowerWithWordWork_spec tier tierPower tierExact units B bound
  obtain ⟨top,spentTop⟩ := historyCapacityUsingWithWork_spec cap tier (fun a => (units a).1) _ read v
  obtain ⟨bottom,spentBottom⟩ := historyCapacityUsingWithWork_spec cap tier (fun a => (units a).1) _ read (heightParent v)
  simp only [historyCutoffFromPowersWithWordWork,historyCutoff,root,ite_false]
  change samplePower*(historyCapacityUsingWithWork cap v).1/(historyCapacityUsingWithWork cap (heightParent v)).1 = _ ∧
    (historyCapacityUsingWithWork cap v).2+(historyCapacityUsingWithWork cap (heightParent v)).2+8 ≤ _
  rw [sampleExact,top,bottom]
  refine ⟨rfl,?_⟩
  calc
    _ ≤ (height+1)*(B+8*(tier+1)+17)+(height+1)*(B+8*(tier+1)+17)+8 :=
      Nat.add_le_add_right (Nat.add_le_add spentTop spentBottom) 8
    _ = _ := by ring

/-- Include construction of both powers in the word bound for a cutoff. -/
def historyCutoffWithArithmeticWordWork (sampleTier tier : ℕ)
    (units : HeightNode V height → ℕ × ℕ) (v : HeightNode V height) : ℕ × ℕ :=
  let sample := twoPowerWithWordWork sampleTier
  let bound := twoPowerWithWordWork tier
  let checked := historyCutoffFromPowersWithWordWork sample.1 bound.1 tier units v
  (checked.1,checked.2+sample.2+bound.2+4)

theorem historyCutoffWithArithmeticWordWork_spec (sampleTier tier : ℕ)
    (units : HeightNode V height → ℕ × ℕ) (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := historyCutoffWithArithmeticWordWork sampleTier tier units v
    out.1 = historyCutoff sampleTier tier (fun a => (units a).1) v ∧
      out.2 ≤ 2*(height+1)*(B+8*(tier+1)+17)+6*(sampleTier+tier)+18 := by
  obtain ⟨value,work⟩ := historyCutoffFromPowersWithWordWork_spec sampleTier tier (2^sampleTier) (2^tier)
    rfl rfl units B bound v
  simp only [historyCutoffWithArithmeticWordWork,twoPowerWithWordWork_spec,value,true_and]
  omega

private def extendHistoryWithWordWork {A : Type*} (next : A) : List A → List A × ℕ
  | [] => ([next],3)
  | a::rest =>
    let extended := extendHistoryWithWordWork next rest
    (a::extended.1,extended.2+4)

private theorem extendHistoryWithWordWork_spec {A : Type*} (next : A) (row : List A) :
    extendHistoryWithWordWork next row = (row++[next],4*row.length+3) := by
  induction row with
  | nil => rfl
  | cons a rest ih =>
    simp only [extendHistoryWithWordWork,ih,List.cons_append,List.length_cons]
    congr 1

private def heightPrefixRowsFromWithWordWork (current todo : List V)
    (fits : current.length+todo.length ≤ height) : List (HeightNode V height) × ℕ :=
  let node : HeightNode V height := ⟨current,le_trans (Nat.le_add_right _ _) fits⟩
  match todo with
  | [] => ([node],4)
  | x::rest =>
    let extended := extendHistoryWithWordWork x current
    have room : extended.1.length+rest.length ≤ height := by
      simp only [extended,extendHistoryWithWordWork_spec,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
      have available : current.length+(rest.length+1) ≤ height := fits
      omega
    let more := heightPrefixRowsFromWithWordWork extended.1 rest room
    (node::more.1,extended.2+more.2+7)
termination_by structural todo

omit [DecidableEq V] [Fintype V] in
private theorem heightPrefixRowsFromWithWordWork_spec (current todo : List V)
    (fits : current.length+todo.length ≤ height) :
    let out := heightPrefixRowsFromWithWordWork current todo fits
    out.1.map Subtype.val = todo.inits.map (fun initial => current++initial) ∧
      out.2 ≤ (todo.length+1)*(4*(current.length+todo.length)+12) := by
  induction todo generalizing current with
  | nil =>
    change [current] = [current++[]] ∧ 4 ≤ 1*(4*(current.length+0)+12)
    simp
  | cons x rest ih =>
    have room : (current++[x]).length+rest.length ≤ height := by
      simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
      have available : current.length+(rest.length+1) ≤ height := fits
      omega
    let tail := heightPrefixRowsFromWithWordWork (current++[x]) rest room
    obtain ⟨exact,work⟩ := ih (current++[x]) room
    change tail.1.map Subtype.val = _ at exact
    change tail.2 ≤ _ at work
    simp only [heightPrefixRowsFromWithWordWork,extendHistoryWithWordWork_spec]
    change current::(tail.1.map Subtype.val) = _ ∧ 4*current.length+3+tail.2+7 ≤ _
    constructor
    · rw [exact,List.inits_cons,List.map_cons,List.map_map]
      simp [Function.comp_def,List.append_assoc]
    · simp only [List.length_cons,List.length_append,List.length_nil,Nat.zero_add] at work ⊢
      have size : current.length+1+rest.length = current.length+(rest.length+1) := by omega
      rw [size] at work
      rw [Nat.succ_mul (rest.length+1) (4*(current.length+(rest.length+1))+12)]
      omega

/-- Enumerate the actual prefixes of a stored history in order. -/
def historyAncestorRowsWithWordWork (node : HeightNode V height) : List (HeightNode V height) × ℕ :=
  heightPrefixRowsFromWithWordWork [] node.val (by simpa using node.property)

theorem historyAncestorRowsWithWordWork_spec (node : HeightNode V height) :
    let out := historyAncestorRowsWithWordWork node
    out.1.map Subtype.val = node.val.inits ∧ out.1.length = node.val.length+1 ∧
      (∀ a, a ∈ out.1 ↔ a ∈ historyAncestors node) ∧ out.2 ≤ (height+1)*(4*height+12) := by
  let out := historyAncestorRowsWithWordWork node
  obtain ⟨exact,work⟩ := heightPrefixRowsFromWithWordWork_spec (height := height) [] node.val (by simpa using node.property)
  have shape : out.1.map Subtype.val = node.val.inits := by
    simpa [out,historyAncestorRowsWithWordWork] using exact
  have length : out.1.length = node.val.length+1 := by
    have same := congrArg List.length shape
    simpa only [List.length_map,List.length_inits] using same
  refine ⟨shape,length,?_,?_⟩
  · intro a
    have on : a ∈ out.1 ↔ a.val ∈ out.1.map Subtype.val := by
      constructor
      · exact List.mem_map_of_mem
      · intro on
        obtain ⟨b,seen,same⟩ := List.mem_map.mp on
        exact (Subtype.ext same : b = a) ▸ seen
    rw [on,shape,List.mem_inits,mem_historyAncestors]
  · have cap : out.2 ≤ (node.val.length+1)*(4*node.val.length+12) := by
      simpa only [out,historyAncestorRowsWithWordWork,List.length_nil,Nat.zero_add] using work
    exact cap.trans (by gcongr <;> exact node.property)

private def minHistoryRowsWithWordWork {A : Type*} (read : A → ℕ × ℕ) (upper : ℕ) : List A → ℕ × ℕ
  | [] => (upper,2)
  | a::rest =>
    let row := read a
    let tail := minHistoryRowsWithWordWork read upper rest
    (min row.1 tail.1,row.2+tail.2+10)

private theorem minHistoryRowsWithWordWork_spec {A : Type*} (read : A → ℕ × ℕ) (upper B : ℕ)
    (rows : List A) (reads : ∀ a ∈ rows, (read a).2 ≤ B) :
    let out := minHistoryRowsWithWordWork read upper rows
    out.1 ≤ upper ∧ (∀ a ∈ rows, out.1 ≤ (read a).1) ∧
      (∀ lower ≤ upper, (∀ a ∈ rows, lower ≤ (read a).1) → lower ≤ out.1) ∧
      out.2 ≤ rows.length*(B+10)+2 := by
  induction rows with
  | nil => simp [minHistoryRowsWithWordWork]
  | cons a rest ih =>
    have front := reads a List.mem_cons_self
    let tail := minHistoryRowsWithWordWork read upper rest
    obtain ⟨cap,small,large,work⟩ := ih (fun b on => reads b (List.mem_cons_of_mem _ on))
    change min (read a).1 tail.1 ≤ upper ∧
      (∀ b ∈ a::rest, min (read a).1 tail.1 ≤ (read b).1) ∧
      (∀ lower ≤ upper, (∀ b ∈ a::rest, lower ≤ (read b).1) → lower ≤ min (read a).1 tail.1) ∧
      (read a).2+tail.2+10 ≤ (a::rest).length*(B+10)+2
    refine ⟨(min_le_right _ _).trans cap,?_,?_,?_⟩
    · intro b on
      rcases List.mem_cons.mp on with rfl | still
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (small b still)
    · intro lower bound below
      exact le_min (below a List.mem_cons_self)
        (large lower bound (fun b on => below b (List.mem_cons_of_mem _ on)))
    · change tail.2 ≤ rest.length*(B+10)+2 at work
      rw [List.length_cons,Nat.succ_mul rest.length (B+10)]
      omega

/-- Minimum capped capacity along the actual stored prefixes of a history.
Includes construction of the prefix rows and arithmetic in the minimum. -/
def historyCapacityFromRowsWithWordWork (tier power : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (node : HeightNode V height) : ℕ × ℕ :=
  let ancestors := historyAncestorRowsWithWordWork node
  let minimum := minHistoryRowsWithWordWork (rootCappedCapacityFromPowerWithWordWork tier power units) power ancestors.1
  (minimum.1,ancestors.2+minimum.2+5)

theorem historyCapacityFromRowsWithWordWork_spec (tier power : ℕ) (exactPower : power = 2^tier)
    (units : HeightNode V height → ℕ × ℕ) (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (node : HeightNode V height) :
    let out := historyCapacityFromRowsWithWordWork tier power units node
    out.1 = historyCapacityUnits tier (fun a => (units a).1) node ∧
      out.2 ≤ (height+1)*(B+8*(tier+1)+4*height+39)+7 := by
  let read := rootCappedCapacityFromPowerWithWordWork tier power units
  let ancestors := historyAncestorRowsWithWordWork node
  let minimum := minHistoryRowsWithWordWork read power ancestors.1
  have exact (a) := rootCappedCapacityFromPowerWithWordWork_spec tier power exactPower units B bound a
  obtain ⟨_,length,contains,form⟩ := historyAncestorRowsWithWordWork_spec node
  obtain ⟨top,small,large,work⟩ := minHistoryRowsWithWordWork_spec read power (B+8*(tier+1)+17) ancestors.1
    (fun a _ => (exact a).2)
  refine ⟨?_,?_⟩
  · change minimum.1 = historyCapacityUnits tier (fun a => (units a).1) node
    apply le_antisymm
    · unfold historyCapacityUnits
      apply le_inf'
      intro a on
      exact (small a ((contains a).mpr on)).trans_eq (exact a).1
    · apply large
      · rw [exactPower]
        exact historyCapacityUnits_bounded tier (fun a => (units a).1) node
      · intro a on
        rw [(exact a).1]
        exact historyCapacityUnits_le tier (fun a => (units a).1) (mem_historyAncestors.mp ((contains a).mp on))
  · change ancestors.2+minimum.2+5 ≤ _
    change minimum.2 ≤ ancestors.1.length*(B+8*(tier+1)+17+10)+2 at work
    change ancestors.1.length = node.val.length+1 at length
    have spent : minimum.2 ≤ (height+1)*(B+8*(tier+1)+17+10)+2 := work.trans (by
      rw [length]
      gcongr
      exact node.property)
    have cap : ancestors.2 ≤ (height+1)*(4*height+12) := form
    calc
      _ ≤ (height+1)*(4*height+12)+((height+1)*(B+8*(tier+1)+17+10)+2)+5 :=
        Nat.add_le_add_right (Nat.add_le_add cap spent) 5
      _ = _ := by ring

private def historyDropLastWithWordWork {A : Type*} : List A → List A × ℕ
  | [] => ([],2)
  | [_] => ([],4)
  | a::b::rest =>
    let shortened := historyDropLastWithWordWork (b::rest)
    (a::shortened.1,shortened.2+7)

private theorem historyDropLastWithWordWork_spec {A : Type*} (row : List A) :
    let out := historyDropLastWithWordWork row
    out.1 = row.dropLast ∧ out.2 ≤ 7*row.length+2 := by
  induction row with
  | nil => exact ⟨rfl,le_rfl⟩
  | cons a rest ih =>
    cases rest with
    | nil => simp [historyDropLastWithWordWork]
    | cons b rest =>
      obtain ⟨value,work⟩ := ih
      simp only [historyDropLastWithWordWork,List.dropLast_cons_cons,value,true_and]
      simp only [List.length_cons] at work ⊢
      omega

private def heightParentHistoryWithWordWork (v : HeightNode V height) : HeightNode V height × ℕ :=
  let rows := historyDropLastWithWordWork v.val
  have fits : rows.1.length ≤ height := by
    rw [(historyDropLastWithWordWork_spec v.val).1]
    exact (List.dropLast_prefix v.val).length_le.trans v.property
  (⟨rows.1,fits⟩,rows.2+3)

omit [DecidableEq V] [Fintype V] in
private theorem heightParentHistoryWithWordWork_spec (v : HeightNode V height) :
    let out := heightParentHistoryWithWordWork v
    out.1 = heightParent v ∧ out.2 ≤ 7*height+5 := by
  obtain ⟨same,spent⟩ := historyDropLastWithWordWork_spec v.val
  refine ⟨Subtype.ext same,?_⟩
  have bound := Nat.mul_le_mul_left 7 v.property
  change (historyDropLastWithWordWork v.val).2+3 ≤ _
  omega

/-- Use the stored history prefixes and cached powers when computing one
rounding cutoff. The tally includes building the parent history. -/
def historyCutoffFromRowsWithWordWork (samplePower tierPower tier : ℕ)
    (units : HeightNode V height → ℕ × ℕ) (v : HeightNode V height) : ℕ × ℕ :=
  if v = heightRoot then (samplePower,4) else
    let parent := heightParentHistoryWithWordWork v
    let top := historyCapacityFromRowsWithWordWork tier tierPower units v
    let bottom := historyCapacityFromRowsWithWordWork tier tierPower units parent.1
    (samplePower*top.1/bottom.1,top.2+bottom.2+parent.2+9)

theorem historyCutoffFromRowsWithWordWork_spec (sampleTier tier samplePower tierPower : ℕ)
    (sampleExact : samplePower = 2^sampleTier) (tierExact : tierPower = 2^tier)
    (units : HeightNode V height → ℕ × ℕ) (B : ℕ) (bound : ∀ v, (units v).2 ≤ B) (v : HeightNode V height) :
    let out := historyCutoffFromRowsWithWordWork samplePower tierPower tier units v
    out.1 = historyCutoff sampleTier tier (fun a => (units a).1) v ∧
      out.2 ≤ 2*(height+1)*(B+8*(tier+1)+4*height+39)+7*height+28 := by
  by_cases root : v = heightRoot
  · simp [historyCutoffFromRowsWithWordWork,historyCutoff,root,sampleExact]
  let parent := heightParentHistoryWithWordWork v
  obtain ⟨parentExact,parentWork⟩ := heightParentHistoryWithWordWork_spec v
  obtain ⟨top,topWork⟩ := historyCapacityFromRowsWithWordWork_spec tier tierPower tierExact units B bound v
  obtain ⟨bottom,bottomWork⟩ := historyCapacityFromRowsWithWordWork_spec tier tierPower tierExact units B bound parent.1
  simp only [historyCutoffFromRowsWithWordWork,historyCutoff,root,ite_false]
  change samplePower*(historyCapacityFromRowsWithWordWork tier tierPower units v).1 /
      (historyCapacityFromRowsWithWordWork tier tierPower units parent.1).1 = _ ∧ _
  constructor
  · rw [sampleExact,top,bottom,parentExact]
  · change (historyCapacityFromRowsWithWordWork tier tierPower units v).2 +
      (historyCapacityFromRowsWithWordWork tier tierPower units parent.1).2 + parent.2 + 9 ≤ _
    let C := (height+1)*(B+8*(tier+1)+4*height+39)+7
    calc
      _ ≤ C+C+(7*height+5)+9 := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add topWork bottomWork) parentWork) 9
      _ = _ := by
        dsimp only [C]
        ring

private def finiteAllWithWork {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) : Bool × ℕ :=
  let rows := s.map (rowWithWork checks)
  (decide (¬ (rows.filter fun r => r.2.1 = false).Nonempty),∑ r ∈ rows, r.2.2)

private theorem finiteAllWithWork_spec {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) (B : ℕ)
    (cap : ∀ i ∈ s, (checks i).2 ≤ B) :
    let out := finiteAllWithWork checks s
    (out.1 = true ↔ ∀ i ∈ s, (checks i).1 = true) ∧ out.2 ≤ s.card*B := by
  refine ⟨?_,rowWork_le s checks B cap⟩
  simp only [finiteAllWithWork,decide_eq_true_eq]
  constructor
  · intro no i hi
    by_contra bad
    have flag : (checks i).1 = false := Bool.eq_false_of_not_eq_true bad
    exact no ⟨rowWithWork checks i,mem_filter.mpr ⟨mem_map_of_mem _ hi,flag⟩⟩
  · rintro all ⟨r,hr⟩
    obtain ⟨present,flag⟩ := mem_filter.mp hr
    obtain ⟨i,hi,rfl⟩ := mem_map.mp present
    exact Bool.noConfusion (flag.symm.trans (all i hi))

/-- Check every ancestor using one metered cutoff computation. -/
def thresholdPathWithWork (m : ℕ) (cutoff : HeightNode V height → ℕ × ℕ)
    (ancestors : Finset (HeightNode V height)) (sample : historySample V height m) : Bool × ℕ :=
  finiteAllWithWork (fun a => let c := cutoff a; (decide ((sample a).val < c.1),c.2)) ancestors

omit [Fintype V] [DecidableEq V] in
theorem thresholdPathWithWork_spec (m : ℕ) (cutoff : HeightNode V height → ℕ × ℕ)
    (ancestors : Finset (HeightNode V height)) (sample : historySample V height m)
    (B : ℕ) (cap : ∀ a ∈ ancestors, (cutoff a).2 ≤ B) :
    let out := thresholdPathWithWork m cutoff ancestors sample
    (out.1 = true ↔ thresholdPath m (fun a => (cutoff a).1) ancestors sample) ∧
      out.2 ≤ ancestors.card*B := by
  simpa only [thresholdPathWithWork,thresholdPath,decide_eq_true_eq] using
    finiteAllWithWork_spec (fun a => let c := cutoff a; (decide ((sample a).val < c.1),c.2)) ancestors B cap

/-- Evaluate all ancestor cutoffs for one rounded tree leg. -/
def historyLegWithWork (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (sample : historySample V height (2^sampleTier)) (v : HeightNode V height) : Bool × ℕ :=
  thresholdPathWithWork _ (historyCutoffWithWork sampleTier tier units) (historyAncestors v) sample

theorem historyLegWithWork_spec (sampleTier tier : ℕ) (units : HeightNode V height → ℕ × ℕ)
    (B : ℕ) (cap : ∀ a, (units a).2 ≤ B)
    (sample : historySample V height (2^sampleTier)) (v : HeightNode V height) :
    let H := height+1
    let out := historyLegWithWork sampleTier tier units sample v
    (out.1 = true ↔ thresholdPath _ (historyCutoff sampleTier tier (fun a => (units a).1))
      (historyAncestors v) sample) ∧ out.2 ≤ 2*H^2*B := by
  let H := height+1
  let cutoff := historyCutoffWithWork sampleTier tier units
  let anc := historyAncestors v
  have each (a : HeightNode V height) := historyCutoffWithWork_spec sampleTier tier units B cap a
  obtain ⟨chosen, work⟩ := thresholdPathWithWork_spec _ cutoff anc sample (2*H*B) (fun a _ => (each a).2)
  have exactValues : (fun a => (cutoff a).1) = historyCutoff sampleTier tier (fun a => (units a).1) :=
    funext fun a => (each a).1
  refine ⟨exactValues ▸ chosen,work.trans ?_⟩
  calc
    _ ≤ H*(2*H*B) := Nat.mul_le_mul_right _ (historyAncestors_card_le v)
    _ = _ := by ring


private def finiteAnyWithWork {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) : Bool × ℕ :=
  let all := finiteAllWithWork (fun i => let row := checks i; (!row.1,row.2)) s
  (!all.1,all.2)

private theorem finiteAnyWithWork_spec {I : Type*} (checks : I → Bool × ℕ) (s : Finset I) (B : ℕ)
    (cap : ∀ i ∈ s, (checks i).2 ≤ B) :
    let out := finiteAnyWithWork checks s
    (out.1 = true ↔ ∃ i ∈ s, (checks i).1 = true) ∧ out.2 ≤ s.card*B := by
  let negated := fun i => let row := checks i; (!row.1,row.2)
  obtain ⟨value, cost⟩ := finiteAllWithWork_spec negated s B cap
  refine ⟨?_,cost⟩
  change (!(finiteAllWithWork negated s).1) = true ↔ _
  have no : (finiteAllWithWork negated s).1 = false ↔ ¬ (finiteAllWithWork negated s).1 = true := by
    cases (finiteAllWithWork negated s).1 <;> simp
  rw [Bool.not_eq_true', no, value]
  simp only [negated, Bool.not_eq_true', not_forall, exists_prop]
  exact exists_congr (fun i => and_congr_right fun _ => by cases (checks i).1 <;> simp)

section Forest

variable {W : Type*} [LinearOrder W] [Fintype W] {h : ℕ}

private def forestUnitsFromWeights (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (edge : HeightForestVertex W h × HeightForestVertex W h) : ℕ :=
  if edge ∈ links then
    let cost := weight edge
    if cost = 0 then scale
    else roundedWeightedCapacity cost (charges (forestNetworkCopy.prodMap forestNetworkCopy edge))
  else 0

private def roundedForestLinksFromWeights (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample W h scale) : Arcs (HeightForestVertex W h) :=
  let units := forestUnitsFromWeights links weight charges scale
  links.filter fun e => weight e = 0 ∨
    ∃ tier : Fin (scale.log2+1),
      let root := heightForestRoot e.1
      let seed := sample root tier
      let side := roundingArcSide e
      let hist := roundingArcHistory e
      seed.1.val < 2^tier.val ∧
        thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
          (fun u => units (heightForestLegArc root side u))) (historyAncestors hist) (seed.2 side)

/-- All trials share the stored forest and hop values. -/
def roundedForestTrialsFromWeights (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) : Arcs (HeightForestVertex W h) :=
  univ.biUnion fun i => roundedForestLinksFromWeights links weight charges scale (sample i)

private def forestUnitsWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (edge : HeightForestVertex W h × HeightForestVertex W h) : ℕ × ℕ :=
  if edge ∈ links then
    let cost := weight edge
    (if cost.1 = 0 then scale else roundedWeightedCapacity cost.1
      (charges (forestNetworkCopy.prodMap forestNetworkCopy edge)),cost.2)
  else (0,0)

omit [Fintype W] in
private theorem forestUnitsWithWork_le (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (edge : HeightForestVertex W h × HeightForestVertex W h) :
    (forestUnitsWithWork links weight charges scale edge).2 ≤ B := by
  unfold forestUnitsWithWork
  split
  · exact bound edge
  · exact Nat.zero_le B

private def forestUnitsWithChargeWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ × ℕ) (scale : ℕ)
    (edge : HeightForestVertex W h × HeightForestVertex W h) : ℕ × ℕ :=
  let on := memFinsetWithWordWork edge links
  if on.1 then
    let cost := weight edge
    if cost.1 = 0 then (scale, on.2+cost.2+6)
    else
      let charge := charges (forestNetworkCopy.prodMap forestNetworkCopy edge)
      let units := roundedWeightedCapacityWithWordWork cost.1 charge.1
      (units.1, on.2+cost.2+charge.2+units.2+13)
  else (0, on.2+4)

omit [Fintype W] in
private theorem forestUnitsWithChargeWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ × ℕ) (scale Wt Q C : ℕ)
    (wt : ∀ e, (weight e).2 ≤ Wt) (charge : ∀ e, (charges e).1 ≤ Q ∧ (charges e).2 ≤ C)
    (edge : HeightForestVertex W h × HeightForestVertex W h) :
    let out := forestUnitsWithChargeWork links weight charges scale edge
    out.1 = (forestUnitsWithWork links weight (fun e => (charges e).1) scale edge).1 ∧
      out.2 ≤ 12*links.card+Wt+6*Q+C+36 := by
  let on := memFinsetWithWordWork edge links
  let cost := weight edge
  let read := charges (forestNetworkCopy.prodMap forestNetworkCopy edge)
  let units := roundedWeightedCapacityWithWordWork cost.1 read.1
  obtain ⟨found, scans⟩ := memFinsetWithWordWork_spec edge links
  change on.2 ≤ _ at scans
  have pay : cost.2 ≤ Wt := wt edge
  obtain ⟨magnitude, lookup⟩ := charge (forestNetworkCopy.prodMap forestNetworkCopy edge)
  change read.2 ≤ C at lookup
  have readLe : read.1/cost.1 ≤ Q := (Nat.div_le_self _ _).trans magnitude
  obtain ⟨exactUnits, charged⟩ := roundedWeightedCapacityWithWordWork_spec cost.1 read.1
  by_cases present : edge ∈ links
  · by_cases free : cost.1 = 0
    · simp only [forestUnitsWithChargeWork, forestUnitsWithWork, present, found, decide_true,
        ite_true, show (weight edge).1 = 0 from free]
      exact ⟨True.intro, by change on.2+cost.2+6 ≤ _; omega⟩
    · simp only [forestUnitsWithChargeWork, forestUnitsWithWork, present, found, decide_true, ite_true,
        show (weight edge).1 ≠ 0 from free, ite_false]
      change units.1 = _ ∧ on.2+cost.2+read.2+units.2+13 ≤ _
      exact ⟨exactUnits, by change units.2 = _ at charged; omega⟩
  · simp only [forestUnitsWithChargeWork, forestUnitsWithWork, present, found, decide_false,
      Bool.false_eq_true, ite_false]
    exact ⟨True.intro, by change on.2+4 ≤ _; omega⟩

private def roundedForestTierWithWork
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) : Bool × ℕ :=
  let root := heightForestRoot e.1
  let seed := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  if seed.1.val < 2^tier.val then
    historyLegWithWork (scale.log2+1) tier.val (fun u => units (heightForestLegArc root side u)) (seed.2 side) hist
  else (false,0)

private theorem roundedForestTierWithWork_spec
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale B : ℕ) (bound : ∀ e, (units e).2 ≤ B) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) :
    let out := roundedForestTierWithWork units scale sample e tier
    let root := heightForestRoot e.1
    let seed := sample root tier
    let side := roundingArcSide e
    let hist := roundingArcHistory e
    (out.1 = true ↔ seed.1.val < 2^tier.val ∧
      thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
        (fun u => (units (heightForestLegArc root side u)).1)) (historyAncestors hist) (seed.2 side)) ∧
      out.2 ≤ 2*(h+1)^2*B := by
  let root := heightForestRoot e.1
  let seed := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  by_cases chosen : seed.1.val < 2^tier.val
  · simpa only [roundedForestTierWithWork, root, seed, side, hist, chosen, ite_true, true_and] using
      historyLegWithWork_spec (scale.log2+1) tier.val (fun u => units (heightForestLegArc root side u))
        B (fun u => bound (heightForestLegArc root side u)) (seed.2 side) hist
  · simp [roundedForestTierWithWork, root, seed, chosen]

private def roundedForestLinkWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample W h scale) (e : HeightForestVertex W h × HeightForestVertex W h) : Bool × ℕ :=
  let cost := weight e
  if cost.1 = 0 then (true,cost.2)
  else
    let units := forestUnitsWithWork links weight charges scale
    let selected := finiteAnyWithWork (roundedForestTierWithWork units scale sample e) univ
    (selected.1,cost.2+selected.2)

private theorem roundedForestLinkWithWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) :
    let out := roundedForestLinkWithWork links weight charges scale sample e
    let units := forestUnitsWithWork links weight charges scale
    (out.1 = true ↔ (weight e).1 = 0 ∨ ∃ tier : Fin (scale.log2+1),
      let root := heightForestRoot e.1
      let seed := sample root tier
      let side := roundingArcSide e
      let hist := roundingArcHistory e
      seed.1.val < 2^tier.val ∧
        thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
          (fun u => (units (heightForestLegArc root side u)).1)) (historyAncestors hist) (seed.2 side)) ∧
    out.2 ≤ (1+(scale.log2+1)*(2*(h+1)^2))*B := by
  let units := forestUnitsWithWork links weight charges scale
  let checked := roundedForestTierWithWork units scale sample e
  have tierCap (t : Fin (scale.log2+1)) := roundedForestTierWithWork_spec units scale B
    (forestUnitsWithWork_le links weight charges scale B bound) sample e t
  by_cases free : (weight e).1 = 0
  · simp only [roundedForestLinkWithWork,free,ite_true,true_or,true_and]
    exact (bound e).trans (Nat.le_mul_of_pos_left _ (by omega))
  · obtain ⟨chosen,work⟩ := finiteAnyWithWork_spec checked univ (2*(h+1)^2*B) (fun t _ => (tierCap t).2)
    simp only [roundedForestLinkWithWork, free, ite_false, false_or]
    refine ⟨?_,?_⟩
    · rw [chosen]
      simpa only [mem_univ, true_and] using exists_congr (fun tier => (tierCap tier).1)
    · calc
        _ ≤ B+(scale.log2+1)*(2*(h+1)^2*B) := Nat.add_le_add (bound e) (by simpa only [card_univ,Fintype.card_fin] using work)
        _ = _ := by ring


omit [Fintype W] in
private theorem forestUnitsWithWork_eq (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ) :
    (fun e => (forestUnitsWithWork links weight charges scale e).1) =
      forestUnitsFromWeights links (fun e => (weight e).1) charges scale := by
  funext e
  by_cases present : e ∈ links
  · by_cases free : (weight e).1 = 0 <;> simp [forestUnitsWithWork, forestUnitsFromWeights, present, free]
  · simp [forestUnitsWithWork, forestUnitsFromWeights, present]

private def roundedForestLinksWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (sample : ForestRoundingSample W h scale) : Arcs (HeightForestVertex W h) × ℕ :=
  let rows := links.map (rowWithWork (roundedForestLinkWithWork links weight charges scale sample))
  ((rows.filter fun r => r.2.1 = true).image Prod.fst,∑ r ∈ rows, r.2.2)

private theorem roundedForestLinksWithWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (sample : ForestRoundingSample W h scale) :
    let out := roundedForestLinksWithWork links weight charges scale sample
    out.1 = roundedForestLinksFromWeights links (fun e => (weight e).1) charges scale sample ∧
      out.2 ≤ links.card*((1+(scale.log2+1)*(2*(h+1)^2))*B) := by
  let checks := roundedForestLinkWithWork links weight charges scale sample
  let row := rowWithWork checks
  let rows := links.map row
  have details (e : HeightForestVertex W h × HeightForestVertex W h) :=
    roundedForestLinkWithWork_spec links weight charges scale B bound sample e
  refine ⟨?_,rowWork_le links checks _ (fun e _ => (details e).2)⟩
  ext e
  let units := forestUnitsFromWeights links (fun e => (weight e).1) charges scale
  let allowed := fun e : HeightForestVertex W h × HeightForestVertex W h =>
    (weight e).1 = 0 ∨ ∃ tier : Fin (scale.log2+1),
      let root := heightForestRoot e.1
      let seed := sample root tier
      let side := roundingArcSide e
      let hist := roundingArcHistory e
      seed.1.val < 2^tier.val ∧
        thresholdPath (forestSeedSize scale) (historyCutoff (scale.log2+1) tier.val
          (fun u => units (heightForestLegArc root side u))) (historyAncestors hist) (seed.2 side)
  have selected (a : HeightForestVertex W h × HeightForestVertex W h) :
      (checks a).1 = true ↔ allowed a := by
    have spec := (details a).1
    dsimp only at spec
    simpa only [checks, allowed, units, congrFun (forestUnitsWithWork_eq links weight charges scale)] using spec
  change e ∈ (rows.filter fun r => r.2.1 = true).image Prod.fst ↔ e ∈ links.filter allowed
  constructor
  · intro he
    obtain ⟨result,present,rfl⟩ := mem_image.mp he
    obtain ⟨inside,pass⟩ := mem_filter.mp present
    obtain ⟨a,ha,rfl⟩ := mem_map.mp inside
    exact mem_filter.mpr ⟨ha,(selected a).mp pass⟩
  · intro he
    obtain ⟨inside, pass⟩ := mem_filter.mp he
    exact mem_image.mpr ⟨row e,mem_filter.mpr ⟨mem_map_of_mem _ inside,(selected e).mpr pass⟩,rfl⟩

/-- Count original weight reads over the rounded links in every trial. Each
trial's graph and measured work are computed together. -/
def roundedForestTrialsWithWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) : Arcs (HeightForestVertex W h) × ℕ :=
  let evaluate := fun i => roundedForestLinksWithWork links weight charges scale (sample i)
  let rows := univ.map (rowWithWork evaluate)
  (rows.biUnion (fun r => r.2.1),∑ r ∈ rows, r.2.2)

theorem roundedForestTrialsWithWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials B : ℕ)
    (bound : ∀ e, (weight e).2 ≤ B) (sample : ForestTrialArray W h scale trials) :
    let out := roundedForestTrialsWithWork links weight charges scale trials sample
    out.1 = roundedForestTrialsFromWeights links (fun e => (weight e).1) charges scale trials sample ∧
      out.2 ≤ trials*(links.card*((1+(scale.log2+1)*(2*(h+1)^2))*B)) := by
  let evaluate := fun i => roundedForestLinksWithWork links weight charges scale (sample i)
  let row := rowWithWork evaluate
  let rows := univ.map row
  have each (i : Fin trials) := roundedForestLinksWithWork_spec links weight charges scale B bound (sample i)
  refine ⟨?_,?_⟩
  · ext e
    change e ∈ rows.biUnion (fun r => r.2.1) ↔
      e ∈ univ.biUnion (fun i => roundedForestLinksFromWeights links (fun e => (weight e).1) charges scale (sample i))
    constructor
    · intro he
      obtain ⟨result,present,contains⟩ := mem_biUnion.mp he
      obtain ⟨i,_,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨i, mem_univ _, (each i).1 ▸ contains⟩
    · intro he
      obtain ⟨i,_,contains⟩ := mem_biUnion.mp he
      exact mem_biUnion.mpr ⟨row i,mem_map_of_mem _ (mem_univ i),(each i).1.symm ▸ contains⟩
  · simpa only [roundedForestTrialsWithWork,card_univ,Fintype.card_fin] using
      rowWork_le univ evaluate _ (fun i _ => (each i).2)

/-! Count seed reads separately from the existing weight reads. -/

private def rowWithSeedReads {I A : Type*} (f : I → A × ℕ × ℕ) : I ↪ I × (A × ℕ × ℕ) :=
  ⟨fun i => (i,f i),fun _ _ same => congrArg Prod.fst same⟩

private theorem rowSeedReads_le {I A : Type*} (s : Finset I) (f : I → A × ℕ × ℕ) (B : ℕ)
    (each : ∀ i ∈ s, (f i).2.2 ≤ B) :
    (∑ row ∈ s.map (rowWithSeedReads f), row.2.2.2) ≤ s.card*B := by
  rw [sum_map]
  calc
    _ ≤ ∑ _ ∈ s, B := sum_le_sum each
    _ = _ := by simp

private theorem rowFirstReads_le {I A : Type*} (s : Finset I) (f : I → A × ℕ × ℕ) (B : ℕ)
    (each : ∀ i ∈ s, (f i).2.1 ≤ B) :
    (∑ row ∈ s.map (rowWithSeedReads f), row.2.2.1) ≤ s.card*B := by
  rw [sum_map]
  calc
    _ ≤ ∑ _ ∈ s, B := sum_le_sum each
    _ = _ := by simp

private def finiteAnyWithSeedReads {I : Type*} (checks : I → Bool × ℕ × ℕ) (s : Finset I) : Bool × ℕ × ℕ :=
  let rows := s.map (rowWithSeedReads checks)
  (decide ((rows.filter fun r => r.2.1 = true).Nonempty),∑ r ∈ rows, r.2.2.1,∑ r ∈ rows, r.2.2.2)

private theorem finiteAnyWithSeedReads_value {I : Type*} (checks : I → Bool × ℕ × ℕ) (s : Finset I) :
    (finiteAnyWithSeedReads checks s).1 = true ↔ ∃ i ∈ s, (checks i).1 = true := by
  let rows := s.map (rowWithSeedReads checks)
  change decide ((rows.filter fun row => row.2.1 = true).Nonempty) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨r, member⟩
    obtain ⟨packed, flag⟩ := mem_filter.mp member
    obtain ⟨i, inside, rfl⟩ := mem_map.mp packed
    exact ⟨i, inside, flag⟩
  · rintro ⟨i, inside, flag⟩
    exact ⟨rowWithSeedReads checks i, mem_filter.mpr ⟨mem_map_of_mem _ inside, flag⟩⟩

private theorem finiteAnyWithSeedReads_spec {I : Type*} (checks : I → Bool × ℕ × ℕ)
    (s : Finset I) (B : ℕ) (cap : ∀ i ∈ s, (checks i).2.2 ≤ B) :
    let out := finiteAnyWithSeedReads checks s
    (out.1,out.2.1) = finiteAnyWithWork (fun i => ((checks i).1,(checks i).2.1)) s ∧
      out.2.2 ≤ s.card*B := by
  let projection := fun i => ((checks i).1,(checks i).2.1)
  have newHasOne := finiteAnyWithSeedReads_value checks s
  have oldHasOne := (finiteAnyWithWork_spec projection s (∑ i ∈ s, (checks i).2.1)
    (fun i mem => single_le_sum (f := fun j => (checks j).2.1) (fun _ _ => zero_le) mem)).1
  refine ⟨Prod.ext (Bool.eq_iff_iff.mpr (newHasOne.trans oldHasOne.symm)) ?_,rowSeedReads_le s checks B cap⟩
  dsimp only [finiteAnyWithSeedReads,finiteAnyWithWork,finiteAllWithWork]
  rw [sum_map,sum_map]
  rfl

private def roundedForestTierWithSeedReads
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) : Bool × ℕ × ℕ :=
  let root := heightForestRoot e.1
  let seed := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  if seed.1.val < 2^tier.val then
    let ancestors := historyAncestors hist
    let cutoffs := historyCutoffWithWork (scale.log2+1) tier.val (fun u => units (heightForestLegArc root side u))
    let chosen := thresholdPathWithWork _ cutoffs ancestors (seed.2 side)
    (chosen.1,chosen.2,1+ancestors.card)
  else (false,0,1)

private theorem roundedForestTierWithSeedReads_spec
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSample W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) :
    let out := roundedForestTierWithSeedReads units scale sample e tier
    (out.1,out.2.1) = roundedForestTierWithWork units scale sample e tier ∧ out.2.2 ≤ h+2 := by
  by_cases gate : (sample (heightForestRoot e.1) tier).1.val < 2^tier.val
  · have card := historyAncestors_card_le (roundingArcHistory e)
    simp only [roundedForestTierWithSeedReads,roundedForestTierWithWork,historyLegWithWork,gate,ite_true]
    exact ⟨True.intro,by omega⟩
  · simp only [roundedForestTierWithSeedReads,roundedForestTierWithWork,gate,ite_false]
    exact ⟨True.intro,by omega⟩

private def finiteAllWithSeedWork {I : Type*} (checks : I → Bool × ℕ × ℕ) (s : Finset I) : Bool × ℕ × ℕ :=
  let rows := s.map (rowWithSeedReads checks)
  (decide (¬ (rows.filter fun row => row.2.1 = false).Nonempty),
    ∑ row ∈ rows, row.2.2.1,∑ row ∈ rows, row.2.2.2)

private theorem finiteAllWithSeedWork_spec {I : Type*} (checks : I → Bool × ℕ × ℕ)
    (s : Finset I) (B : ℕ) (bound : ∀ i ∈ s, (checks i).2.2 ≤ B) :
    let out := finiteAllWithSeedWork checks s
    (out.1,out.2.1) = finiteAllWithWork (fun i => ((checks i).1,(checks i).2.1)) s ∧
      out.2.2 ≤ s.card*B := by
  let rows := s.map (rowWithSeedReads checks)
  let project := fun i => ((checks i).1,(checks i).2.1)
  have all : (finiteAllWithSeedWork checks s).1 = true ↔ ∀ i ∈ s, (checks i).1 = true := by
    change decide (¬ (rows.filter fun row => row.2.1 = false).Nonempty) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · intro pass i member
      by_contra falseFlag
      have flag := Bool.eq_false_of_not_eq_true falseFlag
      exact pass ⟨rowWithSeedReads checks i,mem_filter.mpr ⟨mem_map_of_mem _ member,flag⟩⟩
    · rintro pass ⟨row,member⟩
      obtain ⟨packed,flag⟩ := mem_filter.mp member
      obtain ⟨i,inside,rfl⟩ := mem_map.mp packed
      exact Bool.noConfusion (flag.symm.trans (pass i inside))
  have old := (finiteAllWithWork_spec project s (∑ i ∈ s, (checks i).2.1)
    (fun i mem => single_le_sum (f := fun j => (checks j).2.1) (fun _ _ => zero_le) mem)).1
  refine ⟨Prod.ext (Bool.eq_iff_iff.mpr (all.trans old.symm)) ?_,rowSeedReads_le s checks B bound⟩
  dsimp only [finiteAllWithSeedWork,finiteAllWithWork]
  rw [sum_map,sum_map]
  rfl

/-- Evaluate one individually metered sample for each ancestor in a path test. -/
def thresholdPathWithSeedWork (m : ℕ) (cutoff : HeightNode W h → ℕ × ℕ)
    (ancestors : Finset (HeightNode W h)) (sample : HeightNode W h → Fin m × ℕ) : Bool × ℕ × ℕ :=
  finiteAllWithSeedWork (fun node =>
    let stop := cutoff node
    let read := sample node
    (decide (read.1.val < stop.1),stop.2,read.2)) ancestors

omit [LinearOrder W] [Fintype W] in
theorem thresholdPathWithSeedWork_spec (m : ℕ) (cutoff : HeightNode W h → ℕ × ℕ)
    (ancestors : Finset (HeightNode W h)) (sample : HeightNode W h → Fin m × ℕ)
    (B : ℕ) (bound : ∀ node ∈ ancestors, (sample node).2 ≤ B) :
    let out := thresholdPathWithSeedWork m cutoff ancestors sample
    (out.1,out.2.1) = thresholdPathWithWork m cutoff ancestors (fun node => (sample node).1) ∧
      out.2.2 ≤ ancestors.card*B :=
  finiteAllWithSeedWork_spec (fun node =>
    let stop := cutoff node
    let read := sample node
    (decide (read.1.val < stop.1),stop.2,read.2)) ancestors B bound

abbrev ForestRoundingSampleWithSeedWork (W : Type*) (h scale : ℕ) :=
  W → Fin (scale.log2+1) → (Fin (forestSeedSize scale) × ℕ) ×
    (Bool → HeightNode W h → Fin (forestSeedSize scale) × ℕ)

def forestRoundingSampleValues (scale : ℕ) (sample : ForestRoundingSampleWithSeedWork W h scale) :
    ForestRoundingSample W h scale := fun root tier =>
  let pair := sample root tier
  (pair.1.1,fun side node => (pair.2 side node).1)

private def roundedForestTierWithSeedWork
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSampleWithSeedWork W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) : Bool × ℕ × ℕ :=
  let root := heightForestRoot e.1
  let draw := sample root tier
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  if draw.1.1.val < 2^tier.val then
    let cutoffs := historyCutoffWithWork (scale.log2+1) tier.val (fun node => units (heightForestLegArc root side node))
    let passed := thresholdPathWithSeedWork _ cutoffs (historyAncestors hist) (draw.2 side)
    (passed.1,passed.2.1,draw.1.2+passed.2.2)
  else (false,0,draw.1.2)

private theorem roundedForestTierWithSeedWork_spec
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (sample : ForestRoundingSampleWithSeedWork W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1))
    (B : ℕ) (gateBound : ∀ root i, (sample root i).1.2 ≤ B)
    (testBound : ∀ root i side node, ((sample root i).2 side node).2 ≤ B) :
    let out := roundedForestTierWithSeedWork units scale sample e tier
    (out.1,out.2.1) = roundedForestTierWithWork units scale (forestRoundingSampleValues scale sample) e tier ∧
      out.2.2 ≤ (h+2)*B := by
  let root := heightForestRoot e.1
  let side := roundingArcSide e
  let hist := roundingArcHistory e
  let ancestors := historyAncestors hist
  let cutoffs := historyCutoffWithWork (scale.log2+1) tier.val
    (fun node => units (heightForestLegArc root side node))
  have opening := gateBound root tier
  by_cases openGate : (sample (heightForestRoot e.1) tier).1.1.val < 2^tier.val
  · obtain ⟨preserves,meter⟩ := thresholdPathWithSeedWork_spec _ cutoffs ancestors ((sample root tier).2 side) B
      (fun node _ => testBound root tier side node)
    simp only [roundedForestTierWithSeedWork,roundedForestTierWithWork,forestRoundingSampleValues,
      openGate,ite_true,historyLegWithWork]
    refine ⟨preserves,?_⟩
    exact (Nat.add_le_add opening
      (meter.trans (Nat.mul_le_mul_right B (historyAncestors_card_le hist)))).trans_eq (by ring)
  · simp only [roundedForestTierWithSeedWork,roundedForestTierWithWork,forestRoundingSampleValues,
      openGate,ite_false,true_and]
    exact opening.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- Uniform per-access bound for the gate and ancestor readers. -/
def forestSampleWorkBound {scale : ℕ} (sample : ForestRoundingSampleWithSeedWork W h scale) (B : ℕ) : Prop :=
  ∀ root tier,
    (sample root tier).1.2 ≤ B ∧ ∀ side node, ((sample root tier).2 side node).2 ≤ B

private abbrev ForestTierCheck (W : Type*) (h scale : ℕ) :=
  (HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ) →
    HeightForestVertex W h × HeightForestVertex W h → Fin (scale.log2+1) → Bool × ℕ × ℕ

private def ValidForestTierCheck {scale : ℕ} (check : ForestTierCheck W h scale)
    (sample : ForestRoundingSample W h scale) (bound : ℕ) : Prop :=
  ∀ units e tier,
    let result := check units e tier
    (result.1,result.2.1) = roundedForestTierWithWork units scale sample e tier ∧ result.2.2 ≤ bound

@[inline] private def roundedForestLinkWithSeedTally
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) (e : HeightForestVertex W h × HeightForestVertex W h) : Bool × ℕ × ℕ :=
  let cost := weight e
  if cost.1 = 0 then (true,cost.2,0)
  else
    let selected := finiteAnyWithSeedReads (check units e) univ
    (selected.1,cost.2+selected.2.1,selected.2.2)

private theorem roundedForestLinkWithSeedTally_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) (sample : ForestRoundingSample W h scale) (B : ℕ)
    (valid : ValidForestTierCheck check sample B) (e : HeightForestVertex W h × HeightForestVertex W h) :
    let out := roundedForestLinkWithSeedTally weight (forestUnitsWithWork links weight charges scale) scale check e
    (out.1,out.2.1) = roundedForestLinkWithWork links weight charges scale sample e ∧
      out.2.2 ≤ (scale.log2+1)*B := by
  let units := forestUnitsWithWork links weight charges scale
  let checked := check units e
  have each (tier : Fin (scale.log2+1)) := valid units e tier
  obtain ⟨same,reads⟩ := finiteAnyWithSeedReads_spec checked univ B (fun i _ => (each i).2)
  have keys : (fun i => ((checked i).1,(checked i).2.1)) = roundedForestTierWithWork units scale sample e :=
    funext fun i => (each i).1
  rw [keys] at same
  by_cases free : (weight e).1 = 0
  · simp [roundedForestLinkWithSeedTally,roundedForestLinkWithWork,free]
  · simp only [roundedForestLinkWithSeedTally,roundedForestLinkWithWork,free,ite_false]
    constructor
    · rw [← same]
    · simpa only [card_univ,Fintype.card_fin] using reads

@[inline] private def roundedForestLinksWithSeedTally (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  let rows := links.map (rowWithSeedReads (roundedForestLinkWithSeedTally weight units scale check))
  ((rows.filter fun r => r.2.1 = true).image Prod.fst,∑ r ∈ rows, r.2.2.1,∑ r ∈ rows, r.2.2.2)

private theorem roundedForestLinksWithSeedTally_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale : ℕ)
    (check : ForestTierCheck W h scale) (sample : ForestRoundingSample W h scale) (B : ℕ)
    (valid : ValidForestTierCheck check sample B) :
    let out := roundedForestLinksWithSeedTally links weight (forestUnitsWithWork links weight charges scale) scale check
    (out.1,out.2.1) = roundedForestLinksWithWork links weight charges scale sample ∧
      out.2.2 ≤ links.card*((scale.log2+1)*B) := by
  let checked := roundedForestLinkWithSeedTally weight (forestUnitsWithWork links weight charges scale) scale check
  let prev := roundedForestLinkWithWork links weight charges scale sample
  have each (e) := roundedForestLinkWithSeedTally_spec links weight charges scale check sample B valid e
  refine ⟨Prod.ext ?_ ?_,rowSeedReads_le links checked _ (fun e _ => (each e).2)⟩
  · ext e
    change e ∈ ((links.map (rowWithSeedReads checked)).filter fun r => r.2.1 = true).image Prod.fst ↔
      e ∈ ((links.map (rowWithWork prev)).filter fun r => r.2.1 = true).image Prod.fst
    simp only [mem_image,mem_filter,mem_map]
    constructor
    · rintro ⟨row,⟨⟨k,mem,rfl⟩,yes⟩,rfl⟩
      exact ⟨rowWithWork prev k,⟨⟨k,mem,rfl⟩,(congrArg Prod.fst (each k).1) ▸ yes⟩,rfl⟩
    · rintro ⟨row,⟨⟨k,mem,rfl⟩,yes⟩,rfl⟩
      exact ⟨rowWithSeedReads checked k,⟨⟨k,mem,rfl⟩,(congrArg Prod.fst (each k).1).symm ▸ yes⟩,rfl⟩
  · dsimp only [roundedForestLinksWithSeedTally,roundedForestLinksWithWork]
    rw [sum_map,sum_map]
    exact sum_congr rfl (fun e _ => congrArg Prod.snd (each e).1)

@[inline] private def roundedForestTrialsWithSeedTally (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ) (scale trials : ℕ)
    (check : Fin trials → ForestTierCheck W h scale) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  let evaluate := fun i => roundedForestLinksWithSeedTally links weight units scale (check i)
  let rows := univ.map (rowWithSeedReads evaluate)
  (rows.biUnion (fun r => r.2.1),∑ r ∈ rows, r.2.2.1,∑ r ∈ rows, r.2.2.2)

private theorem roundedForestTrialsWithSeedTally_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (check : Fin trials → ForestTierCheck W h scale) (sample : ForestTrialArray W h scale trials)
    (B : ℕ) (valid : ∀ i, ValidForestTierCheck (check i) (sample i) B) :
    let out := roundedForestTrialsWithSeedTally links weight (forestUnitsWithWork links weight charges scale) scale trials check
    (out.1,out.2.1) = roundedForestTrialsWithWork links weight charges scale trials sample ∧
      out.2.2 ≤ trials*(links.card*((scale.log2+1)*B)) := by
  let evaluate := fun i : Fin trials => roundedForestLinksWithSeedTally links weight (forestUnitsWithWork links weight charges scale) scale (check i)
  let prev := fun i : Fin trials => roundedForestLinksWithWork links weight charges scale (sample i)
  have each (i : Fin trials) := roundedForestLinksWithSeedTally_spec links weight charges scale
    (check i) (sample i) B (valid i)
  refine ⟨Prod.ext ?_ ?_,?_⟩
  · ext e
    change e ∈ (univ.map (rowWithSeedReads evaluate)).biUnion (fun r => r.2.1) ↔
      e ∈ (univ.map (rowWithWork prev)).biUnion (fun r => r.2.1)
    constructor
    · intro he
      obtain ⟨row,present,contains⟩ := mem_biUnion.mp he
      obtain ⟨i,inside,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨rowWithWork prev i,mem_map_of_mem _ inside,
        congrArg Prod.fst (each i).1 ▸ contains⟩
    · intro he
      obtain ⟨row,present,contains⟩ := mem_biUnion.mp he
      obtain ⟨i,inside,rfl⟩ := mem_map.mp present
      exact mem_biUnion.mpr ⟨rowWithSeedReads evaluate i,mem_map_of_mem _ inside,
        (congrArg Prod.fst (each i).1).symm ▸ contains⟩
  · dsimp only [roundedForestTrialsWithSeedTally,roundedForestTrialsWithWork]
    rw [sum_map,sum_map]
    exact sum_congr rfl (fun i _ => congrArg Prod.snd (each i).1)
  · simpa only [roundedForestTrialsWithSeedTally,card_univ,Fintype.card_fin] using
      rowSeedReads_le univ evaluate _ (fun i _ => (each i).2)

/-- Count the root gates and ancestor sample reads. Retain the earlier
weight tally as the middle field. -/
def roundedForestTrialsWithSeedReads (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  roundedForestTrialsWithSeedTally links weight (forestUnitsWithWork links weight charges scale) scale trials
    (fun i units => roundedForestTierWithSeedReads units scale (sample i))

theorem roundedForestTrialsWithSeedReads_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray W h scale trials) :
    let out := roundedForestTrialsWithSeedReads links weight charges scale trials sample
    (out.1,out.2.1) = roundedForestTrialsWithWork links weight charges scale trials sample ∧
      out.2.2 ≤ trials*(links.card*((scale.log2+1)*(h+2))) :=
  roundedForestTrialsWithSeedTally_spec links weight charges scale trials
    (fun i units => roundedForestTierWithSeedReads units scale (sample i)) sample (h+2)
    (fun i units => roundedForestTierWithSeedReads_spec units scale (sample i))

abbrev ForestTrialArrayWithSeedWork (W : Type*) (h scale trials : ℕ) :=
  Fin trials → ForestRoundingSampleWithSeedWork W h scale

/-- Aggregate the work returned by the sampled gates and ancestor tests. -/
def roundedForestTrialsWithSeedWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork W h scale trials) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  roundedForestTrialsWithSeedTally links weight (forestUnitsWithWork links weight charges scale) scale trials
    (fun i units => roundedForestTierWithSeedWork units scale (sample i))

theorem roundedForestTrialsWithSeedWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork W h scale trials) (B : ℕ)
    (cap : ∀ i, forestSampleWorkBound (sample i) B) :
    let out := roundedForestTrialsWithSeedWork links weight charges scale trials sample
    let plain := fun i => forestRoundingSampleValues scale (sample i)
    (out.1,out.2.1) = roundedForestTrialsWithWork links weight charges scale trials plain ∧
      out.2.2 ≤ trials*(links.card*((scale.log2+1)*((h+2)*B))) :=
  roundedForestTrialsWithSeedTally_spec links weight charges scale trials
    (fun i units => roundedForestTierWithSeedWork units scale (sample i))
    (fun i => forestRoundingSampleValues scale (sample i)) ((h+2)*B)
    (fun i units e tier => roundedForestTierWithSeedWork_spec units scale (sample i) e tier B
      (fun root k => (cap i root k).1) (fun root k side node => (cap i root k).2 side node))

private theorem roundedForestTierWithSeedWork_charge_spec
    (units prior : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale S U Wt : ℕ) (sample : ForestRoundingSampleWithSeedWork W h scale)
    (equal : ∀ e, (units e).1 = (prior e).1) (cap : ∀ e, (units e).2 ≤ U)
    (oldCap : ∀ e, (prior e).2 ≤ Wt) (seedCap : forestSampleWorkBound sample S)
    (e : HeightForestVertex W h × HeightForestVertex W h) (tier : Fin (scale.log2+1)) :
    let out := roundedForestTierWithSeedWork units scale sample e tier
    let old := roundedForestTierWithSeedWork prior scale sample e tier
    out.1 = old.1 ∧ out.2.1 ≤ 2*(h+1)^2*U ∧ out.2.2 ≤ (h+2)*S := by
  let plain := forestRoundingSampleValues scale sample
  have tracked (read : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ) :=
    roundedForestTierWithSeedWork_spec read scale sample e tier S
      (fun root k => (seedCap root k).1) (fun root k side node => (seedCap root k).2 side node)
  obtain ⟨value, work⟩ := roundedForestTierWithWork_spec units scale U cap plain e tier
  have oldValue := (roundedForestTierWithWork_spec prior scale Wt oldCap plain e tier).1
  have same : (roundedForestTierWithWork units scale plain e tier).1 =
      (roundedForestTierWithWork prior scale plain e tier).1 := by
    apply Bool.eq_iff_iff.mpr
    exact value.trans (by simpa only [equal] using oldValue.symm)
  refine ⟨(congrArg Prod.fst (tracked units).1).trans (same.trans (congrArg Prod.fst (tracked prior).1).symm),
    ?_, (tracked units).2⟩
  exact (congrArg Prod.snd (tracked units).1).le.trans work

omit [LinearOrder W] [Fintype W] in
private theorem roundedForestLinkWithSeedTally_charge_spec
    (weight units prior : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale C X Y : ℕ) (check : ForestTierCheck W h scale)
    (e : HeightForestVertex W h × HeightForestVertex W h) (paid : (weight e).2 ≤ C)
    (each : ∀ tier,
      let out := check units e tier
      out.1 = (check prior e tier).1 ∧ out.2.1 ≤ X ∧ out.2.2 ≤ Y) :
    let out := roundedForestLinkWithSeedTally weight units scale check e
    let old := roundedForestLinkWithSeedTally weight prior scale check e
    out.1 = old.1 ∧ out.2.1 ≤ C+(scale.log2+1)*X ∧ out.2.2 ≤ (scale.log2+1)*Y := by
  by_cases free : (weight e).1 = 0
  · simp only [roundedForestLinkWithSeedTally, free, ite_true, true_and, zero_le, and_true]
    exact paid.trans (Nat.le_add_right _ _)
  · have same : (finiteAnyWithSeedReads (check units e) univ).1 =
        (finiteAnyWithSeedReads (check prior e) univ).1 := by
      apply Bool.eq_iff_iff.mpr
      rw [finiteAnyWithSeedReads_value, finiteAnyWithSeedReads_value]
      simp only [fun tier => (each tier).1]
    have first := rowFirstReads_le (univ : Finset (Fin (scale.log2+1))) (check units e) X (fun i _ => (each i).2.1)
    have second := rowSeedReads_le (univ : Finset (Fin (scale.log2+1))) (check units e) Y (fun i _ => (each i).2.2)
    simp only [roundedForestLinkWithSeedTally, free, ite_false]
    refine ⟨same, Nat.add_le_add paid ?_, ?_⟩
    · simpa only [finiteAnyWithSeedReads, card_univ, Fintype.card_fin] using first
    · simpa only [finiteAnyWithSeedReads, card_univ, Fintype.card_fin] using second

omit [Fintype W] in
private theorem roundedForestLinksWithSeedTally_member (links : Arcs (HeightForestVertex W h))
    (weight units : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (scale : ℕ) (check : ForestTierCheck W h scale) (e : HeightForestVertex W h × HeightForestVertex W h) :
    e ∈ (roundedForestLinksWithSeedTally links weight units scale check).1 ↔
      e ∈ links ∧ (roundedForestLinkWithSeedTally weight units scale check e).1 = true := by
  let read := roundedForestLinkWithSeedTally weight units scale check
  let rows := links.map (rowWithSeedReads read)
  change e ∈ (rows.filter fun r => r.2.1 = true).image Prod.fst ↔ _
  constructor
  · intro found
    obtain ⟨row, inside, rfl⟩ := mem_image.mp found
    obtain ⟨listed, pass⟩ := mem_filter.mp inside
    obtain ⟨i, old, rfl⟩ := mem_map.mp listed
    exact ⟨old, pass⟩
  · rintro ⟨listed, pass⟩
    exact mem_image.mpr ⟨rowWithSeedReads read e, mem_filter.mpr ⟨mem_map_of_mem _ listed, pass⟩, rfl⟩

/-- Count the unit reads at the ancestor minima, including the weighted
charge access, and carry the seed reads in a separate tally. -/
def roundedForestTrialsWithChargeWork (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ × ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork W h scale trials) : Arcs (HeightForestVertex W h) × ℕ × ℕ :=
  let units := forestUnitsWithChargeWork links weight charges scale
  roundedForestTrialsWithSeedTally links weight units scale trials
    (fun i read => roundedForestTierWithSeedWork read scale (sample i))

theorem roundedForestTrialsWithChargeWork_spec (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ × ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork W h scale trials) (Wt Q C S : ℕ)
    (weightCap : ∀ e, (weight e).2 ≤ Wt) (chargeCap : ∀ e, (charges e).1 ≤ Q ∧ (charges e).2 ≤ C)
    (seedCap : ∀ i, forestSampleWorkBound (sample i) S) :
    let out := roundedForestTrialsWithChargeWork links weight charges scale trials sample
    let old := roundedForestTrialsWithSeedWork links weight (fun e => (charges e).1) scale trials sample
    let U := 12*links.card+Wt+6*Q+C+36
    out.1 = old.1 ∧ out.2.1 ≤ trials*(links.card*(Wt+(scale.log2+1)*(2*(h+1)^2*U))) ∧
      out.2.2 ≤ trials*(links.card*((scale.log2+1)*((h+2)*S))) := by
  let units := forestUnitsWithChargeWork links weight charges scale
  let prior := forestUnitsWithWork links weight (fun e => (charges e).1) scale
  let U := 12*links.card+Wt+6*Q+C+36
  let X := 2*(h+1)^2*U
  let Y := (h+2)*S
  let check := fun i read => roundedForestTierWithSeedWork read scale (sample i)
  let run := fun i => roundedForestLinksWithSeedTally links weight units scale (check i)
  let old := fun i => roundedForestLinksWithSeedTally links weight prior scale (check i)
  have unit (e : HeightForestVertex W h × HeightForestVertex W h) :=
    forestUnitsWithChargeWork_spec links weight charges scale Wt Q C weightCap chargeCap e
  have tier (i : Fin trials) (e : HeightForestVertex W h × HeightForestVertex W h) (t : Fin (scale.log2+1)) :=
    roundedForestTierWithSeedWork_charge_spec units prior scale S U Wt (sample i)
      (fun a => (unit a).1) (fun a => (unit a).2) (forestUnitsWithWork_le links weight (fun a => (charges a).1) scale Wt weightCap)
      (seedCap i) e t
  have link (i : Fin trials) (e : HeightForestVertex W h × HeightForestVertex W h) :=
    roundedForestLinkWithSeedTally_charge_spec weight units prior scale Wt X Y (check i) e (weightCap e) (tier i e)
  have graph (i : Fin trials) : (run i).1 = (old i).1 := by
    ext e
    change e ∈ (roundedForestLinksWithSeedTally links weight units scale (check i)).1 ↔
      e ∈ (roundedForestLinksWithSeedTally links weight prior scale (check i)).1
    rw [roundedForestLinksWithSeedTally_member, roundedForestLinksWithSeedTally_member, (link i e).1]
  have unitWork (i : Fin trials) : (run i).2.1 ≤ links.card*(Wt+(scale.log2+1)*X) :=
    rowFirstReads_le links (roundedForestLinkWithSeedTally weight units scale (check i)) _ (fun a _ => (link i a).2.1)
  have seedWork (i : Fin trials) : (run i).2.2 ≤ links.card*((scale.log2+1)*Y) :=
    rowSeedReads_le links (roundedForestLinkWithSeedTally weight units scale (check i)) _ (fun a _ => (link i a).2.2)
  refine ⟨?_, ?_, ?_⟩
  · ext e
    change e ∈ ((univ : Finset (Fin trials)).map (rowWithSeedReads run)).biUnion (fun r => r.2.1) ↔
      e ∈ ((univ : Finset (Fin trials)).map (rowWithSeedReads old)).biUnion (fun r => r.2.1)
    constructor
    · intro on
      obtain ⟨r, inside, hit⟩ := mem_biUnion.mp on
      obtain ⟨i, hi, rfl⟩ := mem_map.mp inside
      exact mem_biUnion.mpr ⟨rowWithSeedReads old i, mem_map_of_mem _ hi, graph i ▸ hit⟩
    · intro on
      obtain ⟨r, inside, hit⟩ := mem_biUnion.mp on
      obtain ⟨i, hi, rfl⟩ := mem_map.mp inside
      exact mem_biUnion.mpr ⟨rowWithSeedReads run i, mem_map_of_mem _ hi, (graph i).symm ▸ hit⟩
  · simpa only [roundedForestTrialsWithChargeWork, roundedForestTrialsWithSeedTally, card_univ, Fintype.card_fin]
      using rowFirstReads_le (univ : Finset (Fin trials)) run _ (fun i _ => unitWork i)
  · simpa only [roundedForestTrialsWithChargeWork, roundedForestTrialsWithSeedTally, card_univ, Fintype.card_fin]
      using rowSeedReads_le (univ : Finset (Fin trials)) run _ (fun i _ => seedWork i)

end Forest

/-- Metered capacity reads and rounding select only links from the input forest. -/
theorem roundedForestTrialsWithChargeWork_sub {W : Type*} [LinearOrder W] [Fintype W] {h : ℕ}
    (links : Arcs (HeightForestVertex W h))
    (weight : HeightForestVertex W h × HeightForestVertex W h → ℕ × ℕ)
    (charges : ForestNetworkVertex W h × ForestNetworkVertex W h → ℕ × ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork W h scale trials) :
    (roundedForestTrialsWithChargeWork links weight charges scale trials sample).1 ⊆ links := by
  intro e member
  dsimp only [roundedForestTrialsWithChargeWork,roundedForestTrialsWithSeedTally] at member
  obtain ⟨row,onRow,onGraph⟩ := mem_biUnion.mp member
  obtain ⟨i,_,rfl⟩ := mem_map.mp onRow
  dsimp only [rowWithSeedReads,roundedForestLinksWithSeedTally] at onGraph
  obtain ⟨choice,onChoice,rfl⟩ := mem_image.mp onGraph
  obtain ⟨link,onLink,rfl⟩ := mem_map.mp (mem_filter.mp onChoice).1
  exact onLink

end OnlineReachabilityPreservers
