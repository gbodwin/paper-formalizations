import OnlineReachabilityPreservers.ThinSearchWork
import OnlineReachabilityPreservers.SteinerThinRound

/-! Search work in all prefix tests of the thin rounding procedure. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def thinThresholdRow {G : Arcs V} (sample : ThinSample G) : G ↪ (V × V) × ℕ :=
  ⟨fun e => (e.val,(sample e).val),fun _ _ same => Subtype.ext (congrArg Prod.fst same)⟩

/-- Read each arc threshold once. The arc count is supplied by the caller. -/
def prepareThinThresholdRowsWithSeedReads (G : Arcs V) (m : ℕ) (sample : ThinSample G) :
    Finset ((V × V) × ℕ) × ℕ :=
  (G.attach.map (thinThresholdRow sample),m)

/-- Apply the fractional loads to the stored threshold of every arc. -/
def roundedFromThinThresholdRows (rows : Finset ((V × V) × ℕ)) (factor : ℕ) (load : CutLoads V) : Arcs V :=
  (rows.filter fun row => row.2 < factor*2^(load row.1)).image Prod.fst

omit [Fintype V] in
theorem prepareThinThresholdRowsWithSeedReads_spec (G : Arcs V) (m : ℕ) (hm : m = G.card) (sample : ThinSample G) :
    let out := prepareThinThresholdRowsWithSeedReads G m sample
    out.1.card = out.2 ∧ ∀ factor load,
      roundedFromThinThresholdRows out.1 factor load = roundedThinArcs G factor load sample := by
  intro out
  refine ⟨?_,?_⟩
  · change (G.attach.map (thinThresholdRow sample)).card = m
    rw [card_map,card_attach,hm]
  · intro factor load
    change ((G.attach.map (thinThresholdRow sample)).filter fun row =>
      row.2 < factor*2^(load row.1)).image Prod.fst = _
    rw [filter_map,map_eq_image,image_image]
    rfl

private def thinThresholdRowByIndex {G : Arcs V} {m : ℕ} (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) : Fin m ↪ (V × V) × ℕ :=
  let arcAt := arcs.invFun
  ⟨fun i =>
    let position : Fin G.card := ⟨i.val,hm ▸ i.isLt⟩
    ((arcAt position).val,(sample position).val), by
    intro i j same
    have arc : arcs.symm ⟨i.val,hm ▸ i.isLt⟩ = arcs.symm ⟨j.val,hm ▸ j.isLt⟩ :=
      Subtype.ext (congrArg Prod.fst same)
    exact Fin.ext (congrArg (fun k : Fin G.card => k.val) (arcs.symm.injective arc))⟩

/-- Read the original arc and its seed in storage order. The numeric size
is supplied, so the loop does not recalculate the graph cardinality. -/
def prepareThinThresholdRowsByIndex (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) : Finset ((V × V) × ℕ) × ℕ :=
  (univ.map (thinThresholdRowByIndex hm arcs sample),m)

omit [LinearOrder V] [Fintype V] in
theorem prepareThinThresholdRowsByIndex_eq (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) :
    prepareThinThresholdRowsByIndex G m hm arcs sample =
      prepareThinThresholdRowsWithSeedReads G m (fun edge => sample (arcs edge)) := by
  subst m
  refine Prod.ext ?_ rfl
  ext row
  change row ∈ univ.map (thinThresholdRowByIndex rfl arcs sample) ↔
    row ∈ G.attach.map (thinThresholdRow (fun edge => sample (arcs edge)))
  constructor
  · intro present
    obtain ⟨i,_,rfl⟩ := mem_map.mp present
    refine mem_map.mpr ⟨arcs.symm i,mem_attach _ _,?_⟩
    change ((arcs.symm i).val,(sample (arcs (arcs.symm i))).val) = ((arcs.symm i).val,(sample i).val)
    rw [Equiv.apply_symm_apply]
  · intro present
    obtain ⟨e,_,rfl⟩ := mem_map.mp present
    refine mem_map.mpr ⟨arcs e,mem_univ _,?_⟩
    change ((arcs.symm (arcs e)).val,(sample (arcs e)).val) = (e.val,(sample (arcs e)).val)
    rw [Equiv.symm_apply_apply]

private def tabulateFinRowsLoop {A : Type*} (n : ℕ) (row : Fin n → A) :
    (k : ℕ) → k ≤ n → List A → ℕ → List A × ℕ
  | 0, _, acc, work => (acc,work+2)
  | k+1, bound, acc, work =>
    let entry := row ⟨k,Nat.lt_of_succ_le bound⟩
    tabulateFinRowsLoop n row k (Nat.le_of_succ_le bound) (entry::acc) (work+7)

private theorem tabulateFinRowsLoop_spec {A : Type*} (n : ℕ) (row : Fin n → A) (k : ℕ)
    (bound : k ≤ n) (acc : List A) (work : ℕ) :
    tabulateFinRowsLoop n row k bound acc work =
      ((List.finRange k).map (fun i => row ⟨i.val,Nat.lt_of_lt_of_le i.isLt bound⟩) ++ acc,work+7*k+2) := by
  induction k generalizing acc work with
  | zero => simp [tabulateFinRowsLoop]
  | succ k ih =>
    rw [tabulateFinRowsLoop,ih,List.finRange_succ_last,List.map_append,List.map_map]
    refine Prod.ext ?_ (by omega)
    simp only [List.map_cons,List.map_nil,List.append_assoc,List.singleton_append]
    rfl

/-- Construct each of the supplied index rows once. The tally covers the
loop and list construction, with the supplied row operation charged separately. -/
private def tabulateFinRowsWithWordWork {A : Type*} (n : ℕ) (row : Fin n → A) : List A × ℕ :=
  tabulateFinRowsLoop n row n (Nat.le_refl n) [] 2

private theorem tabulateFinRowsWithWordWork_spec {A : Type*} (n : ℕ) (row : Fin n → A) :
    tabulateFinRowsWithWordWork n row = ((List.finRange n).map row,7*n+4) := by
  rw [tabulateFinRowsWithWordWork,tabulateFinRowsLoop_spec]
  exact Prod.ext (by simp) (by omega)

/-- Threshold rows stored as a list with distinct arc keys. -/
abbrev ThinThresholdList (V : Type*) := {rows : List ((V × V) × ℕ) // (rows.map Prod.fst).Nodup}

/-- The late threshold cache as a list with one row per arc. In addition to
indexing and list work, charge each row's two reads, pairing, and dispatch. -/
def prepareThinThresholdListByIndexWithWordWork (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) :
    ThinThresholdList V × ℕ :=
  let row := thinThresholdRowByIndex hm arcs sample
  let stored := tabulateFinRowsWithWordWork m row.toFun
  have distinct : (stored.1.map Prod.fst).Nodup := by
    dsimp only [stored]
    rw [tabulateFinRowsWithWordWork_spec,List.map_map]
    apply (List.nodup_finRange m).map
    intro i j same
    have arc : arcs.symm ⟨i.val,hm ▸ i.isLt⟩ = arcs.symm ⟨j.val,hm ▸ j.isLt⟩ :=
      Subtype.ext same
    exact Fin.ext (congrArg (fun k : Fin G.card => k.val) (arcs.symm.injective arc))
  (⟨stored.1,distinct⟩,stored.2+4*m)

/-- Build the late cache in one pass, exposing the rows as a finite set. -/
def prepareThinThresholdRowsByIndexWithWordWork (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) : Finset ((V × V) × ℕ) × ℕ :=
  let built := prepareThinThresholdListByIndexWithWordWork G m hm arcs sample
  (⟨built.1.val,built.1.property.of_map _⟩,built.2)

omit [LinearOrder V] [Fintype V] in
theorem prepareThinThresholdRowsByIndexWithWordWork_spec (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) :
    let out := prepareThinThresholdRowsByIndexWithWordWork G m hm arcs sample
    out.1 = (prepareThinThresholdRowsByIndex G m hm arcs sample).1 ∧ out.2 = 11*m+4 := by
  let row := thinThresholdRowByIndex hm arcs sample
  have agree := tabulateFinRowsWithWordWork_spec m row
  constructor
  · apply eq_of_veq
    change ↑(tabulateFinRowsWithWordWork m row).1 = ((univ : Finset (Fin m)).map row).val
    rw [agree,Fin.univ_def]
    rfl
  · change (tabulateFinRowsWithWordWork m row).2+4*m = 11*m+4
    rw [agree]
    dsimp only
    omega

omit [Fintype V] in
theorem prepareThinThresholdListByIndexWithWordWork_spec (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) :
    let out := prepareThinThresholdListByIndexWithWordWork G m hm arcs sample
    out.1.val.toFinset = (prepareThinThresholdRowsByIndex G m hm arcs sample).1 ∧
      out.1.val.length = m ∧ (∀ r ∈ out.1.val, r.1 ∈ G) ∧ out.2 = 11*m+4 := by
  let row := thinThresholdRowByIndex hm arcs sample
  have agree := tabulateFinRowsWithWordWork_spec m row
  obtain ⟨rowsEq,work⟩ := prepareThinThresholdRowsByIndexWithWordWork_spec G m hm arcs sample
  refine ⟨?_,?_,?_,work⟩
  · rw [← rowsEq]
    ext r
    let rows := (prepareThinThresholdListByIndexWithWordWork G m hm arcs sample).1.val
    change r ∈ rows.toFinset ↔ r ∈ rows
    exact List.mem_toFinset
  · change (tabulateFinRowsWithWordWork m row).1.length = m
    rw [agree]
    simp
  · change ∀ r ∈ (tabulateFinRowsWithWordWork m row).1, r.1 ∈ G
    rw [agree]
    intro r mem
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
    exact (arcs.invFun ⟨i.val,hm ▸ i.isLt⟩).property


private def thinDoubleLoop : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, value, work => (value, work+2)
  | k+1, value, work => thinDoubleLoop k (value+value) (work+4)

private theorem thinDoubleLoop_spec (k value work : ℕ) :
    thinDoubleLoop k value work = (value*2^k,work+4*k+2) := by
  induction k generalizing value work with
  | zero => simp [thinDoubleLoop]
  | succ k ih =>
    rw [thinDoubleLoop,ih,pow_succ]
    apply Prod.ext
    · dsimp only
      ring
    · dsimp only
      omega

private def thinRoundRowPasses {E : Type*} (factor : ℕ) (load : E → ℕ × ℕ)
    (row : E × ℕ) : Prop := row.2 < factor*2^(load row.1).1

private instance {E : Type*} (factor : ℕ) (load : E → ℕ × ℕ) (row : E × ℕ) :
    Decidable (thinRoundRowPasses factor load row) := inferInstanceAs (Decidable (_ < _))

/-- Scan each threshold row once, with the load callback returning its own work. -/
private def roundThinThresholdListLoop {E : Type*} (factor : ℕ) (load : E → ℕ × ℕ) :
    List (E × ℕ) → List E → ℕ → List E × ℕ
  | [], kept, work => (kept,work+2)
  | (arc,threshold)::rows, kept, work =>
    let counted := load arc
    let power := thinDoubleLoop counted.1 1 0
    let kept' := if threshold < factor*power.1 then arc::kept else kept
    roundThinThresholdListLoop factor load rows kept' (work+counted.2+power.2+10)

private theorem roundThinThresholdListLoop_values {E : Type*} (factor : ℕ) (load : E → ℕ × ℕ)
    (rows : List (E × ℕ)) (kept : List E) (work : ℕ) :
    (roundThinThresholdListLoop factor load rows kept work).1 =
      ((rows.filter (thinRoundRowPasses factor load)).map Prod.fst).reverse ++ kept := by
  induction rows generalizing kept work with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨arc,threshold⟩ := row
    rw [roundThinThresholdListLoop,thinDoubleLoop_spec,ih]
    simp only [Nat.one_mul, List.filter_cons]
    by_cases h : thinRoundRowPasses factor load (arc,threshold)
    · have passed : threshold < factor*2^(load arc).1 := h
      simp [h,passed,List.reverse_cons,List.append_assoc]
    · have failed : ¬ threshold < factor*2^(load arc).1 := h
      simp [h,failed]

private theorem roundThinThresholdListLoop_work {E : Type*} (factor : ℕ) (load : E → ℕ × ℕ)
    (rows : List (E × ℕ)) (kept : List E) (work maxLoad maxRead : ℕ)
    (bounded : ∀ r ∈ rows, (load r.1).1 ≤ maxLoad ∧ (load r.1).2 ≤ maxRead) :
    (roundThinThresholdListLoop factor load rows kept work).2 ≤
      work+2+rows.length*(maxRead+4*maxLoad+12) := by
  induction rows generalizing kept work with
  | nil => simp [roundThinThresholdListLoop]
  | cons row rows ih =>
    obtain ⟨arc,threshold⟩ := row
    have here := bounded (arc,threshold) List.mem_cons_self
    have rest (r) (mem : r ∈ rows) := bounded r (List.mem_cons_of_mem _ mem)
    rw [roundThinThresholdListLoop,thinDoubleLoop_spec]
    refine (ih _ _ rest).trans ?_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only at here ⊢
    omega

/-- A meter for the rounding pass on a stored list with one row per arc.
The load callback accounts for work needed to retrieve each exponent. -/
def roundThinThresholdListWithWordWork (rows : List ((V × V) × ℕ))
    (unique : (rows.map Prod.fst).Nodup) (factor : ℕ) (load : (V × V) → ℕ × ℕ) : Arcs V × ℕ :=
  let out := roundThinThresholdListLoop factor load rows [] 2
  have kept : out.1.Nodup := by
    dsimp only [out]
    rw [roundThinThresholdListLoop_values,List.append_nil,List.nodup_reverse]
    exact ((List.filter_sublist (p := thinRoundRowPasses factor load)).map Prod.fst).nodup unique
  (⟨out.1,kept⟩,out.2)

omit [Fintype V] in
theorem roundThinThresholdListWithWordWork_spec (rows : List ((V × V) × ℕ))
    (unique : (rows.map Prod.fst).Nodup) (factor : ℕ) (load : (V × V) → ℕ × ℕ) :
    (roundThinThresholdListWithWordWork rows unique factor load).1 =
      roundedFromThinThresholdRows rows.toFinset factor (fun e => (load e).1) := by
  apply Finset.ext
  intro e
  change e ∈ ((roundThinThresholdListLoop factor load rows [] 2).1 : Multiset (V × V)) ↔ _
  rw [roundThinThresholdListLoop_values,List.append_nil]
  simp [roundedFromThinThresholdRows, thinRoundRowPasses]
  constructor
  · rintro ⟨threshold,mem,passed⟩
    exact ⟨threshold,mem,of_decide_eq_true passed⟩
  · rintro ⟨threshold,mem,passed⟩
    exact ⟨threshold,mem,decide_eq_true passed⟩

omit [LinearOrder V] [Fintype V] in
theorem roundThinThresholdListWithWordWork_bound (rows : List ((V × V) × ℕ))
    (unique : (rows.map Prod.fst).Nodup) (factor : ℕ) (load : (V × V) → ℕ × ℕ)
    (maxLoad maxRead : ℕ)
    (bounded : ∀ r ∈ rows, (load r.1).1 ≤ maxLoad ∧ (load r.1).2 ≤ maxRead) :
    (roundThinThresholdListWithWordWork rows unique factor load).2 ≤
      4+rows.length*(maxRead+4*maxLoad+12) :=
  roundThinThresholdListLoop_work factor load rows [] 2 maxLoad maxRead bounded

private def thinRoundWorkEntryUsing (G : Arcs V) (m : ℕ) (round : CutLoads V → Arcs V)
    (D : List (V × V)) (i : Fin D.length) : Fin D.length × Bool × ℕ :=
  let fraction := thinCoverRunWithSearchWork G (D.take (i.val+1))
  let arcs := round fraction.1.1
  let reach := reachInWithArcInspections arcs (D.get i).2 (Fintype.card V)
  (i, decide ((D.get i).1 ∉ reach.1), fraction.2+m+reach.2)

private abbrev thinRoundWorkEntry (G : Arcs V) (factor : ℕ) (sample : ThinSample G) :=
  thinRoundWorkEntryUsing G G.card (fun load => roundedThinArcs G factor load sample)

private theorem thinRoundWorkEntry_flag (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (i : Fin D.length) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (thinRoundWorkEntry G factor sample D i).2.1 = true ↔
      (D.get i).1 ∉ reaches
        (roundedThinArcs G factor (thinCoverRun G (D.take (i.val+1))) sample) (D.get i).2 := by
  have earlier : ∀ d ∈ D.take (i.val+1), Reach G d.1 d.2 :=
    fun d hd => feasible d (List.mem_of_mem_take hd)
  have same := (thinCoverRunWithSearchWork_spec G (D.take (i.val+1)) earlier).1
  simp only [thinRoundWorkEntry, thinRoundWorkEntryUsing, reachInWithArcInspections_spec, decide_eq_true_eq, same, reaches]

/-- Individual charges include a scan of the rounded arc set and a
reachability test, in addition to the fractional prefix evaluator. -/
def thinRoundPrefixWorkBound (n m p : ℕ) : ℕ :=
  (p+m*(m.log2+1))*thinSeparatorWorkBound n m+m+n*m

private theorem thinRoundWorkEntry_bound (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (i : Fin D.length) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (thinRoundWorkEntry G factor sample D i).2.2 ≤
      thinRoundPrefixWorkBound (Fintype.card V) G.card D.length := by
  have earlier : ∀ d ∈ D.take (i.val+1), Reach G d.1 d.2 :=
    fun d hd => feasible d (List.mem_of_mem_take hd)
  let P := D.take (i.val+1)
  let result := thinCoverRunWithSearchWork G P
  let n := Fintype.card V
  let m := G.card
  let R := roundedThinArcs G factor result.1.1 sample
  have frac := (thinCoverRunWithSearchWork_spec G P earlier).2.2.2.trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (show P.length ≤ D.length from (List.take_prefix _ _).length_le) _))
  have arcs : R.card ≤ m := card_le_card (roundedThinArcs_subset _ _ _ _)
  change result.2+m+(reachInWithArcInspections R (D.get i).2 n).2 ≤ _
  rw [reachInWithArcInspections_spec R (D.get i).2 n]
  exact Nat.add_le_add (Nat.add_le_add_right frac m) (Nat.mul_le_mul_left _ arcs)

private def thinRoundRunWithSearchWorkUsing (G : Arcs V) (count : Unit → ℕ) (round : CutLoads V → Arcs V)
    (D : List (V × V)) : Arcs V × ℕ :=
  if D.isEmpty then (∅,0) else
    let m := count ()
    let rows := (univ : Finset (Fin D.length)).image (thinRoundWorkEntryUsing G m round D)
    let cost := ∑ row ∈ rows, row.2.2
    if (rows.filter (fun r => r.2.1 = true)).Nonempty then (G,cost)
    else
      let result := thinCoverRunWithSearchWork G D
      (round result.1.1,cost+result.2+m)

/-- Reproduce the ordinary thin fallback and final graph while charging
each fractional replay, rounded-arc scan and reachability test. -/
def thinRoundRunWithSearchWork (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) : Arcs V × ℕ :=
  thinRoundRunWithSearchWorkUsing G (fun _ => G.card) (fun load => roundedThinArcs G factor load sample) D

/-- Run the same thin fallback checks on the precomputed threshold rows. -/
def thinRoundRunFromThresholdRows (G : Arcs V) (m factor : ℕ) (rows : Finset ((V × V) × ℕ))
    (D : List (V × V)) : Arcs V × ℕ :=
  thinRoundRunWithSearchWorkUsing G (fun _ => m) (roundedFromThinThresholdRows rows factor) D

theorem thinRoundRunFromThresholdRows_eq (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (factor : ℕ) (sample : ThinSample G) (D : List (V × V)) :
    let prepared := prepareThinThresholdRowsWithSeedReads G m sample
    thinRoundRunFromThresholdRows G m factor prepared.1 D = thinRoundRunWithSearchWork G factor sample D := by
  intro prepared
  have round : roundedFromThinThresholdRows prepared.1 factor = (fun load => roundedThinArcs G factor load sample) :=
    funext (fun load => (prepareThinThresholdRowsWithSeedReads_spec G m hm sample).2 factor load)
  change thinRoundRunWithSearchWorkUsing G (fun _ => m) (roundedFromThinThresholdRows prepared.1 factor) D =
    thinRoundRunWithSearchWorkUsing G (fun _ => G.card) (fun load => roundedThinArcs G factor load sample) D
  rw [round,hm]

theorem thinRoundRunWithSearchWork_spec (G : Arcs V) (factor : ℕ) (sample : ThinSample G)
    (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := thinRoundRunWithSearchWork G factor sample D
    out.1 = thinRoundRun G factor sample D ∧
      out.2 ≤ (D.length+1)*thinRoundPrefixWorkBound (Fintype.card V) G.card D.length := by
  let rows := (univ : Finset (Fin D.length)).image (thinRoundWorkEntry G factor sample D)
  let cost := ∑ row ∈ rows, row.2.2
  let B := thinRoundPrefixWorkBound (Fintype.card V) G.card D.length
  have same : (rows.filter (fun r => r.2.1 = true)).Nonempty ↔ ThinRoundFailure G factor sample D := by
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨inside, mark⟩ := mem_filter.mp hr
      obtain ⟨i, _, rfl⟩ := mem_image.mp inside
      exact ⟨i, (thinRoundWorkEntry_flag G factor sample D i feasible).mp mark⟩
    · rintro ⟨i, missed⟩
      exact ⟨_, mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ i),
        (thinRoundWorkEntry_flag G factor sample D i feasible).mpr missed⟩⟩
  have work : cost ≤ D.length*B := by
    dsimp only [cost, rows]
    rw [sum_image (fun a _ b _ eq => congrArg Prod.fst eq)]
    calc
      _ ≤ ∑ _ : Fin D.length, B :=
        sum_le_sum (fun i _ => thinRoundWorkEntry_bound G factor sample D i feasible)
      _ = _ := by simp
  by_cases empty : D.isEmpty = true
  · simp [thinRoundRunWithSearchWork, thinRoundRunWithSearchWorkUsing, thinRoundRun, empty]
  by_cases failed : ThinRoundFailure G factor sample D
  · have failed' := same.mpr failed
    simp only [thinRoundRunWithSearchWork, thinRoundRunWithSearchWorkUsing, thinRoundRun, empty, Bool.false_eq_true, ite_false]
    rw [ite_eq_left failed', ite_eq_left failed]
    exact ⟨rfl, work.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))⟩
  · have passed := (not_congr same).mpr failed
    obtain ⟨output, _, _, finalWork⟩ := thinCoverRunWithSearchWork_spec G D feasible
    simp only [thinRoundRunWithSearchWork, thinRoundRunWithSearchWorkUsing, thinRoundRun, empty, Bool.false_eq_true, ite_false]
    rw [ite_eq_right passed, ite_eq_right failed]
    refine ⟨congrArg (fun load => roundedThinArcs G factor load sample) output, ?_⟩
    have cap : (thinCoverRunWithSearchWork G D).2+G.card ≤ B :=
      (Nat.add_le_add_right finalWork _).trans (Nat.le_add_right _ _)
    change cost+(thinCoverRunWithSearchWork G D).2+G.card ≤ (D.length+1)*B
    rw [Nat.add_assoc, Nat.succ_mul]
    exact Nat.add_le_add work cap

private theorem thinRoundWorkEntryUsing_snoc_earlier {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (round : CutLoads (Fin n) → Arcs (Fin n)) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (i : Fin D.length) :
    let next : Fin (D++[d]).length := ⟨i.val,by simp⟩
    (thinRoundWorkEntryUsing G m round (D++[d]) next).2 = (thinRoundWorkEntryUsing G m round D i).2 := by
  let next : Fin (D++[d]).length := ⟨i.val,by simp⟩
  have takeEq : (D++[d]).take (next.val+1) = D.take (i.val+1) :=
    List.take_append_of_le_length (show i.val+1 ≤ D.length from i.isLt)
  have getEq : (D++[d]).get next = D.get i := List.getElem_append_left (i := i.val) i.isLt
  change (thinRoundWorkEntryUsing G m round (D++[d]) next).2 = (thinRoundWorkEntryUsing G m round D i).2
  simp only [thinRoundWorkEntryUsing,takeEq,getEq]

private theorem thinRoundWorkEntryUsing_snoc_last {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (round : CutLoads (Fin n) → Arcs (Fin n)) (D : List (Fin n × Fin n)) (d : Fin n × Fin n) :
    let all := D++[d]
    let last : Fin all.length := ⟨D.length,by simp [all]⟩
    let loads := thinCoverRunWithSearchWork G all
    let reached := reachInWithArcInspections (round loads.1.1) d.2 n
    (thinRoundWorkEntryUsing G m round all last).2 =
      (decide (d.1 ∉ reached.1),loads.2+m+reached.2) := by
  have takeEq : (D++[d]).take (D.length+1) = D++[d] := List.take_of_length_le (by simp)
  have getEq : (D++[d]).get ⟨D.length,by simp⟩ = d := by
    change (D++[d])[D.length]'(by simp) = d
    rw [List.getElem_append_right (le_refl D.length)]
    simp
  dsimp only [thinRoundWorkEntryUsing]
  simp only [takeEq,getEq,Fintype.card_fin]

private noncomputable def thinRoundIndexedTotals {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (round : CutLoads (Fin n) → Arcs (Fin n)) (D : List (Fin n × Fin n)) : Bool × ℕ := by
  classical
  exact (decide (∃ i : Fin D.length, (thinRoundWorkEntryUsing G m round D i).2.1 = true),
    ∑ i : Fin D.length, (thinRoundWorkEntryUsing G m round D i).2.2)

private theorem thinRoundIndexedTotals_snoc {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (round : CutLoads (Fin n) → Arcs (Fin n)) (D : List (Fin n × Fin n)) (d : Fin n × Fin n) :
    let prior := thinRoundIndexedTotals G m round D
    let all := D++[d]
    let index : Fin all.length := ⟨D.length,by simp [all]⟩
    let last := (thinRoundWorkEntryUsing G m round all index).2
    thinRoundIndexedTotals G m round all = (prior.1 || last.1,prior.2+last.2) := by
  classical
  let all := D++[d]
  let into : Fin (D.length+1) ≃ Fin all.length := finCongr (by simp [all])
  let row := thinRoundWorkEntryUsing G m round all
  let prior := thinRoundWorkEntryUsing G m round D
  have earlier (i : Fin D.length) : (row (into i.castSucc)).2 = (prior i).2 :=
    thinRoundWorkEntryUsing_snoc_earlier G m round D d i
  change thinRoundIndexedTotals G m round all =
    ((thinRoundIndexedTotals G m round D).1 || (row (into (Fin.last D.length))).2.1,
      (thinRoundIndexedTotals G m round D).2+(row (into (Fin.last D.length))).2.2)
  apply Prod.ext
  · apply Bool.eq_iff_iff.mpr
    simp only [thinRoundIndexedTotals,decide_eq_true_eq,Bool.or_eq_true]
    constructor
    · rintro ⟨i,missed⟩
      let j := into.symm i
      have step : (row (into j)).2.1 = true := by simpa only [j,Equiv.apply_symm_apply] using missed
      revert step
      refine Fin.lastCases ?_ ?_ j
      · exact Or.inr
      · intro k affected
        rw [earlier] at affected
        exact Or.inl ⟨k,affected⟩
    · rintro (⟨i,missed⟩ | missed)
      · exact ⟨into i.castSucc, by rw [show (row (into i.castSucc)).2 = (prior i).2 from earlier i]; exact missed⟩
      · exact ⟨into (Fin.last D.length),missed⟩
  · change (∑ i : Fin all.length, (row i).2.2) = (∑ i : Fin D.length, (prior i).2.2)+_
    rw [← Equiv.sum_comp into (fun i => (row i).2.2),Fin.sum_univ_castSucc]
    congr 1
    exact sum_congr rfl (fun i _ => congrArg Prod.snd (earlier i))

private structure ThinRoundArrayState (n : ℕ) where
  fractional : FinThinPrefixState n
  rounded : Arcs (Fin n)
  missed : Bool
  testWork : ℕ
  roundWork : ℕ

private abbrev ThinPrefixAdvance (n : ℕ) :=
  FinThinPrefixState n → (Fin n × Fin n) → FinThinPrefixState n

private def thinRoundArrayStep {n : ℕ} (advance : ThinPrefixAdvance n) (m : ℕ)
    (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (prior : ThinRoundArrayState n) (d : Fin n × Fin n) : ThinRoundArrayState n :=
  let fractional := advance prior.fractional d
  let rounded := roundThinThresholdListWithWordWork rows.val rows.property factor (fun e => (fractional.loads.read e,6))
  let reach := reachInWithArcInspections rounded.1 d.2 n
  ⟨fractional,rounded.1,prior.missed || decide (d.1 ∉ reach.1),
    prior.testWork+(fractional.searchWork+m+reach.2),prior.roundWork+rounded.2+9⟩

private def thinRoundArrayFold {n : ℕ} (advance : ThinPrefixAdvance n) (m : ℕ)
    (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) : ThinRoundArrayState n :=
  D.foldl (thinRoundArrayStep advance m rows factor) ⟨FinThinPrefixState.initial n,∅,false,0,0⟩

private def ThinPrefixAdvance.Exact {n : ℕ} (advance : ThinPrefixAdvance n) (G : Arcs (Fin n)) : Prop :=
  ∀ prior P d, prior.fractionalRecord = thinCoverRunWithSearchWork G P →
    (advance prior d).fractionalRecord = thinCoverRunWithSearchWork G (P++[d])

private def thinRoundPrefixAdvance {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) : ThinPrefixAdvance n :=
  thinCoverArrayPrefixStep G m (m*(m.log2+1)+1)

private def thinRoundPrefixAdvanceWithSeparatorWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) : ThinPrefixAdvance n :=
  thinCoverArrayPrefixStepWithSeparatorWork G m (m*(m.log2+1)+1)

private theorem thinRoundPrefixAdvance_exact {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card) :
    (thinRoundPrefixAdvance G m).Exact G :=
  fun prior P d same => (thinCoverArrayPrefixStep_spec G m hm prior P d same).1

private theorem thinRoundPrefixAdvanceWithSeparatorWork_exact {n : ℕ} (G : Arcs (Fin n))
    (m : ℕ) (hm : m = G.card) : (thinRoundPrefixAdvanceWithSeparatorWork G m).Exact G :=
  fun prior P d same => (thinCoverArrayPrefixStepWithSeparatorWork_spec G m hm prior P d same).1

private theorem thinRoundArrayFold_values {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (advance : ThinPrefixAdvance n) (stepExact : advance.Exact G) (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) :
    let out := thinRoundArrayFold advance m rows factor D
    let round := roundedFromThinThresholdRows rows.val.toFinset factor
    out.fractional.fractionalRecord = thinCoverRunWithSearchWork G D ∧
      (out.missed,out.testWork) = thinRoundIndexedTotals G m round D ∧
      (D ≠ [] → out.rounded = round (thinCoverRunWithSearchWork G D).1.1) := by
  let round := roundedFromThinThresholdRows rows.val.toFinset factor
  induction D using List.reverseRecOn with
  | nil =>
    have blank : (emptyFinThinLoads n).read = fun _ => 0 := funext emptyFinThinLoads_read
    simp [thinRoundArrayFold,FinThinPrefixState.initial,FinThinPrefixState.fractionalRecord,
      thinCoverRunWithSearchWork,thinRoundIndexedTotals,blank,(emptyFinThinLoadsWithWordWork_spec n).1]
    rfl
  | append_singleton D d ih =>
    let prior := thinRoundArrayFold advance m rows factor D
    let advanced := thinRoundArrayStep advance m rows factor prior d
    obtain ⟨record,totals,_⟩ := ih
    have foldEq : thinRoundArrayFold advance m rows factor (D++[d]) = advanced := by
      unfold thinRoundArrayFold
      rw [List.foldl_append]
      rfl
    have fraction := stepExact prior.fractional D d record
    change advanced.fractional.fractionalRecord = thinCoverRunWithSearchWork G (D++[d]) at fraction
    have loads := congrArg (fun x : (CutLoads (Fin n) × ℕ) × ℕ => x.1.1) fraction
    have work := congrArg Prod.snd fraction
    change advanced.fractional.loads.read = (thinCoverRunWithSearchWork G (D++[d])).1.1 at loads
    change advanced.fractional.searchWork = (thinCoverRunWithSearchWork G (D++[d])).2 at work
    have rounded := roundThinThresholdListWithWordWork_spec rows.val rows.property factor
      (fun e => (advanced.fractional.loads.read e,6))
    change advanced.rounded = round advanced.fractional.loads.read at rounded
    rw [loads] at rounded
    dsimp only
    rw [foldEq]
    refine ⟨fraction,?_,fun _ => rounded⟩
    let reached := reachInWithArcInspections advanced.rounded d.2 n
    change (prior.missed || decide (d.1 ∉ reached.1),prior.testWork+(advanced.fractional.searchWork+m+reached.2)) = _
    have sumEq := thinRoundIndexedTotals_snoc G m round D d
    dsimp only at sumEq
    rw [thinRoundWorkEntryUsing_snoc_last] at sumEq
    rw [sumEq,← totals,work]
    dsimp only [reached]
    simp only [rounded]
    rfl

@[inline] private def thinRoundRunFromThresholdListUsing {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (advance : ThinPrefixAdvance n) (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) : (Arcs (Fin n) × ℕ) × ℕ :=
  if D.isEmpty then ((∅,0),2)
  else
    let out := thinRoundArrayFold advance m rows factor D
    let result := if out.missed then (G,out.testWork) else (out.rounded,out.testWork+out.fractional.searchWork+m)
    (result,out.fractional.updateWork+out.roundWork+4)

private theorem thinRoundRunFromThresholdListUsing_eq {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (advance : ThinPrefixAdvance n) (stepExact : advance.Exact G) (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) :
    (thinRoundRunFromThresholdListUsing G m advance rows factor D).1 =
      thinRoundRunFromThresholdRows G m factor rows.val.toFinset D := by
  classical
  by_cases empty : D.isEmpty = true
  · simp [thinRoundRunFromThresholdListUsing,thinRoundRunFromThresholdRows,thinRoundRunWithSearchWorkUsing,empty]
  let out := thinRoundArrayFold advance m rows factor D
  let round := roundedFromThinThresholdRows rows.val.toFinset factor
  let entry := thinRoundWorkEntryUsing G m round D
  let checks := (univ : Finset (Fin D.length)).image entry
  obtain ⟨fraction,totals,rounded⟩ := thinRoundArrayFold_values G m advance stepExact rows factor D
  have work := congrArg Prod.snd fraction
  have listed : (∑ row ∈ checks, row.2.2) = out.testWork := by
    dsimp only [checks]
    rw [sum_image (fun a _ b _ eq => congrArg Prod.fst eq)]
    exact (congrArg Prod.snd totals).symm
  have failSeen : (checks.filter (fun r => r.2.1 = true)).Nonempty ↔ out.missed = true := by
    have first := congrArg Prod.fst totals
    change out.missed = (thinRoundIndexedTotals G m round D).1 at first
    rw [first]
    simp only [thinRoundIndexedTotals,decide_eq_true_eq]
    constructor
    · rintro ⟨r,hr⟩
      obtain ⟨seen,fail⟩ := mem_filter.mp hr
      obtain ⟨i,_,rfl⟩ := mem_image.mp seen
      exact ⟨i,fail⟩
    · rintro ⟨i,fail⟩
      exact ⟨entry i,mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ i),fail⟩⟩
  have nonempty : D ≠ [] := by
    intro nil
    exact empty (nil.symm ▸ rfl)
  have graph := rounded nonempty
  change out.rounded = round (thinCoverRunWithSearchWork G D).1.1 at graph
  change out.fractional.searchWork = (thinCoverRunWithSearchWork G D).2 at work
  simp only [thinRoundRunFromThresholdListUsing,thinRoundRunFromThresholdRows,
    thinRoundRunWithSearchWorkUsing,empty,Bool.false_eq_true,ite_false]
  change (if out.missed = true then (G,out.testWork) else (out.rounded,out.testWork+out.fractional.searchWork+m)) =
    (if (checks.filter (fun r => r.2.1 = true)).Nonempty then (G,_)
      else (round (thinCoverRunWithSearchWork G D).1.1,(∑ row ∈ checks,row.2.2)+(thinCoverRunWithSearchWork G D).2+m))
  by_cases misses : out.missed = true
  · rw [ite_eq_left misses,ite_eq_left (failSeen.mpr misses),listed]
  · rw [ite_eq_right misses,ite_eq_right ((not_congr failSeen).mpr misses),listed,graph,work]

private theorem thinRoundArrayFold_fractional {n : ℕ} (advance : ThinPrefixAdvance n) (m : ℕ)
    (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) :
    (thinRoundArrayFold advance m rows factor D).fractional =
      D.foldl advance (FinThinPrefixState.initial n) := by
  induction D using List.reverseRecOn with
  | nil => rfl
  | append_singleton D d ih =>
    simp only [thinRoundArrayFold,List.foldl_append,List.foldl_cons,List.foldl_nil]
    dsimp only [thinRoundArrayStep]
    congr 1

private theorem thinRoundArrayFold_roundWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (advance : ThinPrefixAdvance n) (stepExact : advance.Exact G) (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m) (factor : ℕ)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (thinRoundArrayFold advance m rows factor D).roundWork ≤ D.length*(13+m*(6+4*(m.log2+1)+12)) := by
  let B := m*(6+4*(m.log2+1)+12)
  induction D using List.reverseRecOn with
  | nil => simp [thinRoundArrayFold]
  | append_singleton D d ih =>
    let prior := thinRoundArrayFold advance m rows factor D
    let new := thinRoundArrayStep advance m rows factor prior d
    let load (e : Fin n × Fin n) := (new.fractional.loads.read e,6)
    let rounded := roundThinThresholdListWithWordWork rows.val rows.property factor load
    have foldEq : thinRoundArrayFold advance m rows factor (D++[d]) = new := by
      unfold thinRoundArrayFold
      rw [List.foldl_append]
      rfl
    have oldWork := ih (fun q present => feasible q (List.mem_append_left _ present))
    have record := (thinRoundArrayFold_values G m advance stepExact rows factor (D++[d])).1
    rw [foldEq] at record
    have loadEq := congrArg (fun x : (CutLoads (Fin n) × ℕ) × ℕ => x.1.1) record
    change new.fractional.loads.read = _ at loadEq
    have caps := (thinCoverRunWithSearchWork_spec G (D++[d]) feasible).2.1
    have resolved : ∀ r ∈ rows.val, (load r.1).1 ≤ m.log2+1 ∧ (load r.1).2 ≤ 6 := by
      intro r present
      refine ⟨?_,le_rfl⟩
      change new.fractional.loads.read r.1 ≤ m.log2+1
      rw [loadEq,hm]
      exact caps r.1 (edges r present)
    have roundWork : rounded.2 ≤ 4+B :=
      (roundThinThresholdListWithWordWork_bound rows.val rows.property factor load (m.log2+1) 6 resolved).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _)
    rw [foldEq]
    change prior.roundWork+rounded.2+9 ≤ (D++[d]).length*(13+B)
    calc
      _ ≤ D.length*(13+B)+(4+B)+9 := Nat.add_le_add_right (Nat.add_le_add oldWork roundWork) _
      _ = _ := by simp only [List.length_append,List.length_singleton]; ring

/-- Check the thin prefixes with one incrementally maintained load table and
retain the last rounded graph for the successful branch. -/
def thinRoundRunFromThresholdListWithWordWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) : (Arcs (Fin n) × ℕ) × ℕ :=
  thinRoundRunFromThresholdListUsing G m (thinRoundPrefixAdvance G m) rows factor D

theorem thinRoundRunFromThresholdListWithWordWork_eq {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) :
    (thinRoundRunFromThresholdListWithWordWork G m rows factor D).1 =
      thinRoundRunFromThresholdRows G m factor rows.val.toFinset D :=
  thinRoundRunFromThresholdListUsing_eq G m _ (thinRoundPrefixAdvance_exact G m hm) rows factor D

/-- Check the same thin prefixes with an indexed signed flow in each separator. -/
def thinRoundRunFromThresholdListWithSeparatorWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (rows : ThinThresholdList (Fin n)) (factor : ℕ)
    (D : List (Fin n × Fin n)) : (Arcs (Fin n) × ℕ) × ℕ :=
  thinRoundRunFromThresholdListUsing G m (thinRoundPrefixAdvanceWithSeparatorWork G m) rows factor D

theorem thinRoundRunFromThresholdListWithSeparatorWork_eq {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (rows : ThinThresholdList (Fin n)) (factor : ℕ) (D : List (Fin n × Fin n)) :
    (thinRoundRunFromThresholdListWithSeparatorWork G m rows factor D).1 =
      thinRoundRunFromThresholdRows G m factor rows.val.toFinset D :=
  thinRoundRunFromThresholdListUsing_eq G m _ (thinRoundPrefixAdvanceWithSeparatorWork_exact G m hm) rows factor D

/-- Source-level work for one run of the incremental thin evaluator. -/
def steinerStreamingThinWorkBound (n m p : ℕ) : ℕ :=
  (m*(m.log2+1)+p)*(10*m+8)+3*p+(4*(n*n)+5)+p*(13+m*(6+4*(m.log2+1)+12))+4

/-- A polynomial cap obtained by replacing the base-two logarithm by the arc count. -/
def steinerStreamingThinWorkPolynomial (n m p : ℕ) : ℕ :=
  (m*(m+1)+p)*(10*m+8)+3*p+(4*(n*n)+5)+p*(13+m*(6+4*(m+1)+12))+4

theorem steinerStreamingThinWorkBound_le (n m p : ℕ) :
    steinerStreamingThinWorkBound n m p ≤ steinerStreamingThinWorkPolynomial n m p := by
  unfold steinerStreamingThinWorkBound steinerStreamingThinWorkPolynomial
  have logBound := Nat.log2_le_self m
  gcongr

/-- Bound the additional table construction, updates and rounding work.
The existing search count is preserved, with residual search internals separate. -/
private theorem thinRoundRunFromThresholdListUsing_bound {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (advance : ThinPrefixAdvance n) (stepExact : advance.Exact G) (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m) (factor : ℕ)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) (B : ℕ)
    (updateWork : let out := D.foldl advance (FinThinPrefixState.initial n)
      out.updateWork ≤ (out.updates+D.length)*B+3*D.length+(4*(n*n)+5)) :
    (thinRoundRunFromThresholdListUsing G m advance rows factor D).2 ≤
      (m*(m.log2+1)+D.length)*B+3*D.length+(4*(n*n)+5)+
        D.length*(13+m*(6+4*(m.log2+1)+12))+4 := by
  by_cases empty : D.isEmpty = true
  · simp only [thinRoundRunFromThresholdListUsing,empty,ite_true]
    omega
  let folded := thinRoundArrayFold advance m rows factor D
  have roundWork := thinRoundArrayFold_roundWork G m hm advance stepExact rows edges count factor D feasible
  have sameFraction := thinRoundArrayFold_fractional advance m rows factor D
  have record := (thinRoundArrayFold_values G m advance stepExact rows factor D).1
  rw [sameFraction] at record
  have updates := (thinCoverRunWithSearchWork_spec G D feasible).2.2.1
  rw [← hm] at updates
  have updateCount := congrArg (fun x : (CutLoads (Fin n) × ℕ) × ℕ => x.1.2) record
  have upper := updateWork.trans
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (updateCount.trans_le updates) _)) _) _)
  simp only [thinRoundRunFromThresholdListUsing,empty,Bool.false_eq_true,ite_false]
  change folded.fractional.updateWork+folded.roundWork+4 ≤ _
  rw [sameFraction]
  exact Nat.add_le_add_right (Nat.add_le_add upper roundWork) _

/-- Charge table construction, updates and rounding at every thin check. -/
theorem thinRoundRunFromThresholdListWithWordWork_bound {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m) (factor : ℕ)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (thinRoundRunFromThresholdListWithWordWork G m rows factor D).2 ≤
      steinerStreamingThinWorkBound n m D.length :=
  thinRoundRunFromThresholdListUsing_bound G m hm _ (thinRoundPrefixAdvance_exact G m hm)
    rows edges count factor D feasible (10*m+8) (thinCoverArrayPrefixFold_spec G m hm D).2

/-- Additional word work for a thin run with indexed residual flow. -/
def steinerThinSeparatorWorkBound (n m p : ℕ) : ℕ :=
  steinerStreamingThinWorkBound n m p+(m*(m.log2+1)+p)*thinSeparatorArrayWordCap n m

/-- A polynomial cap for the signed-flow and rounding work of one thin run. -/
def steinerThinSeparatorWorkPolynomial (n m p : ℕ) : ℕ :=
  steinerStreamingThinWorkPolynomial n m p+(m*(m+1)+p)*thinSeparatorArrayWordCap n m

theorem steinerThinSeparatorWorkBound_le (n m p : ℕ) :
    steinerThinSeparatorWorkBound n m p ≤ steinerThinSeparatorWorkPolynomial n m p := by
  unfold steinerThinSeparatorWorkBound steinerThinSeparatorWorkPolynomial
  have streaming := steinerStreamingThinWorkBound_le n m p
  have logBound := Nat.log2_le_self m
  gcongr

theorem thinRoundRunFromThresholdListWithSeparatorWork_bound {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (hm : m = G.card) (rows : ThinThresholdList (Fin n))
    (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m) (factor : ℕ)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (thinRoundRunFromThresholdListWithSeparatorWork G m rows factor D).2 ≤
      steinerThinSeparatorWorkBound n m D.length := by
  apply (thinRoundRunFromThresholdListUsing_bound G m hm _ (thinRoundPrefixAdvanceWithSeparatorWork_exact G m hm)
    rows edges count factor D feasible (10*m+8+thinSeparatorArrayWordCap n m)
    (thinCoverArrayPrefixFoldWithSeparatorWork_spec G m hm D).2).trans_eq
  unfold steinerThinSeparatorWorkBound steinerStreamingThinWorkBound
  ring

end OnlineReachabilityPreservers
