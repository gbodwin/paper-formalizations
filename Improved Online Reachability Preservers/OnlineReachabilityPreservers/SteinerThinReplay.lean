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

/-- Build the late cache in one pass. In addition to the indexing and
list work, charge each row's two reads, pairing, and dispatch. -/
def prepareThinThresholdRowsByIndexWithWordWork (G : Arcs V) (m : ℕ) (hm : m = G.card)
    (arcs : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) : Finset ((V × V) × ℕ) × ℕ :=
  let row := thinThresholdRowByIndex hm arcs sample
  let stored := tabulateFinRowsWithWordWork m row.toFun
  have distinct : stored.1.Nodup := by
    dsimp only [stored]
    rw [tabulateFinRowsWithWordWork_spec]
    exact (List.nodup_finRange m).map row.injective
  (⟨stored.1,distinct⟩,stored.2+4*m)

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

end OnlineReachabilityPreservers
