import OnlineReachabilityPreservers.SeparatorWork
import OnlineReachabilityPreservers.SteinerThinCover

/-! Search inspections across the complete fractional thin-demand run. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Inspect the metered separator and, when it succeeds, rebuild the
interval and filter its outgoing cut for the charge update. -/
def thinSeparatorWorkBound (n m : ℕ) : ℕ :=
  m*residualStepWorkBound n+(2*n^2+n*n^2)+(2*n*m+m)+(2*n*m+2*m)

def thinCoverLoopWithSearchWork (G : Arcs V) (d : V × V) :
    ℕ → CutLoads V → (CutLoads V × ℕ) × ℕ
  | 0, load => ((load, 0), 0)
  | k+1, load =>
    let step := fastThinViolationWithSearchWork G d load
    match step.1 with
    | none => ((load, 0), step.2)
    | some W =>
      let n := Fintype.card V
      let m := G.card
      let cut := outgoingCut (intervalArcs G d) W
      let rest := thinCoverLoopWithSearchWork G d k (doubleCut cut load)
      ((rest.1.1, rest.1.2+1), step.2+(2*n*m+2*m)+rest.2)

theorem thinCoverLoopWithSearchWork_spec (G : Arcs V) (d : V × V) (fuel : ℕ) (load : CutLoads V) :
    let out := thinCoverLoopWithSearchWork G d fuel load
    out.1 = thinCoverLoop G d fuel load ∧
      out.2 ≤ (out.1.2+1)*thinSeparatorWorkBound (Fintype.card V) G.card := by
  induction fuel generalizing load with
  | zero => simp [thinCoverLoopWithSearchWork, thinCoverLoop]
  | succ k ih =>
    let n := Fintype.card V
    let m := G.card
    let B := thinSeparatorWorkBound n m
    let step := fastThinViolationWithSearchWork G d load
    obtain ⟨same, bound⟩ := fastThinViolationWithSearchWork_spec G d load
    change step.1 = fastThinViolation G d load at same
    change step.2 ≤ m*residualStepWorkBound n+(2*n^2+n*n^2)+(2*n*m+m) at bound
    have full : step.2+(2*n*m+2*m) ≤ B := Nat.add_le_add_right bound _
    cases h : step.1 with
    | none =>
      have plain : fastThinViolation G d load = none := same.symm.trans h
      change (fastThinViolationWithSearchWork G d load).1 = none at h
      simp only [thinCoverLoopWithSearchWork, h, thinCoverLoop, plain, true_and, Nat.zero_add, Nat.one_mul]
      exact (Nat.le_add_right _ _).trans full
    | some W =>
      have plain : fastThinViolation G d load = some W := same.symm.trans h
      let cut := outgoingCut (intervalArcs G d) W
      let next := doubleCut cut load
      let tail := thinCoverLoopWithSearchWork G d k next
      obtain ⟨tailSame, tailWork⟩ := ih next
      change tail.1 = _ at tailSame
      change tail.2 ≤ (tail.1.2+1)*B at tailWork
      change (fastThinViolationWithSearchWork G d load).1 = some W at h
      simp only [thinCoverLoopWithSearchWork, h, thinCoverLoop, plain]
      change (tail.1.1, tail.1.2+1) = _ ∧ step.2+(2*n*m+2*m)+tail.2 ≤ (tail.1.2+1+1)*B
      refine ⟨?_, (Nat.add_le_add full tailWork).trans_eq (by ring)⟩
      rw [← tailSame]

private def thinCoverRunWithSearchWorkFrom (G : Arcs V) :
    List (V × V) → CutLoads V → (CutLoads V × ℕ) × ℕ
  | [], load => ((load, 0), 0)
  | d :: D, load =>
    let step := thinCoverLoopWithSearchWork G d (G.card*(G.card.log2+1)+1) load
    let remain := thinCoverRunWithSearchWorkFrom G D step.1.1
    ((remain.1.1, step.1.2+remain.1.2), step.2+remain.2)

private theorem thinCoverRunWithSearchWorkFrom_spec (G : Arcs V) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2)
    (load : CutLoads V) (cap : ∀ e ∈ G, load e ≤ G.card.log2+1) :
    let out := thinCoverRunWithSearchWorkFrom G D load
    out.1.1 = D.foldl (fun l d => thinCoverStep G d l) load ∧
      (∀ e ∈ G, out.1.1 e ≤ G.card.log2+1) ∧
      loadTotal G load+out.1.2 ≤ loadTotal G out.1.1 ∧
      out.2 ≤ (D.length+out.1.2)*thinSeparatorWorkBound (Fintype.card V) G.card := by
  induction D generalizing load with
  | nil => exact ⟨rfl, cap, by simp [thinCoverRunWithSearchWorkFrom], by simp [thinCoverRunWithSearchWorkFrom]⟩
  | cons d D ih =>
    let fuel := G.card*(G.card.log2+1)+1
    let step := thinCoverLoopWithSearchWork G d fuel load
    let rest := thinCoverRunWithSearchWorkFrom G D step.1.1
    let B := thinSeparatorWorkBound (Fintype.card V) G.card
    have reach := feasible d List.mem_cons_self
    obtain ⟨same, firstWork⟩ := thinCoverLoopWithSearchWork_spec G d fuel load
    change step.1 = thinCoverLoop G d fuel load at same
    change step.2 ≤ (step.1.2+1)*B at firstWork
    have thin : step.1.1 = thinCoverStep G d load := congrArg Prod.fst same
    have cap' : ∀ e ∈ G, step.1.1 e ≤ G.card.log2+1 :=
      thin.symm ▸ (thinCoverStep_spec G G (Subset.rfl) d reach load cap).2.1
    have adds : loadTotal G load+step.1.2 ≤ loadTotal G step.1.1 := by
      rw [same]
      exact thinCoverLoop_load_progress G G (Subset.rfl) d reach fuel load cap
    obtain ⟨out, outCap, outAdds, outWork⟩ := ih (fun q hq => feasible q (List.mem_cons_of_mem _ hq)) step.1.1 cap'
    change rest.1.1 = _ at out
    change loadTotal G step.1.1 + rest.1.2 ≤ loadTotal G rest.1.1 at outAdds
    change rest.2 ≤ (D.length+rest.1.2)*B at outWork
    change rest.1.1 = D.foldl (fun l d => thinCoverStep G d l) (thinCoverStep G d load) ∧
      (∀ e ∈ G, rest.1.1 e ≤ G.card.log2+1) ∧
      loadTotal G load+(step.1.2+rest.1.2) ≤ loadTotal G rest.1.1 ∧
      step.2+rest.2 ≤ ((d::D).length+(step.1.2+rest.1.2))*B
    refine ⟨out.trans (congrArg (D.foldl (fun l d => thinCoverStep G d l)) thin), outCap, by omega, ?_⟩
    exact (Nat.add_le_add firstWork outWork).trans_eq (by simp only [List.length_cons]; ring)

/-- Return the actual fractional loads, cut updates and search inspections. -/
def thinCoverRunWithSearchWork (G : Arcs V) (D : List (V × V)) : (CutLoads V × ℕ) × ℕ :=
  thinCoverRunWithSearchWorkFrom G D (fun _ => 0)

theorem thinCoverRunWithSearchWork_spec (G : Arcs V) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := thinCoverRunWithSearchWork G D
    out.1.1 = thinCoverRun G D ∧
      (∀ e ∈ G, out.1.1 e ≤ G.card.log2+1) ∧
      out.1.2 ≤ G.card*(G.card.log2+1) ∧
      out.2 ≤ (D.length+G.card*(G.card.log2+1))*thinSeparatorWorkBound (Fintype.card V) G.card := by
  obtain ⟨same, caps, updates, work⟩ := thinCoverRunWithSearchWorkFrom_spec G D feasible (fun _ => 0)
    (fun _ _ => Nat.zero_le _)
  let out := thinCoverRunWithSearchWork G D
  have total : loadTotal G out.1.1 ≤ G.card*(G.card.log2+1) := by
    unfold loadTotal
    exact (sum_le_sum caps).trans_eq (by simp)
  have updates' : out.1.2 ≤ G.card*(G.card.log2+1) := (Nat.le_add_left ..).trans (updates.trans total)
  exact ⟨same, caps, updates', work.trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_left updates' _))⟩

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

/-- Store each load at the arithmetic address of its pair of vertex labels. -/
abbrev FinThinLoadTable (n : ℕ) := {values : Array ℕ // values.size = n*n}

private def finThinLoadPosition {n : ℕ} (arc : Fin n × Fin n) : Fin (n*n) :=
  ⟨arc.2.val+n*arc.1.val,(finProdFinEquiv arc).isLt⟩

def emptyFinThinLoads (n : ℕ) : FinThinLoadTable n :=
  ⟨Array.replicate (n*n) 0,by simp⟩

def FinThinLoadTable.read {n : ℕ} (table : FinThinLoadTable n) (arc : Fin n × Fin n) : ℕ :=
  let index := finThinLoadPosition arc
  table.val[index.val]'(by rw [table.property]; exact index.isLt)

def FinThinLoadTable.write {n : ℕ} (table : FinThinLoadTable n) (arc : Fin n × Fin n) (value : ℕ) :
    FinThinLoadTable n :=
  let index := finThinLoadPosition arc
  ⟨table.val.set index.val value (by rw [table.property]; exact index.isLt),by simpa using table.property⟩

theorem emptyFinThinLoads_read {n : ℕ} (arc : Fin n × Fin n) : (emptyFinThinLoads n).read arc = 0 := by
  simp [FinThinLoadTable.read,emptyFinThinLoads]

theorem FinThinLoadTable.read_write {n : ℕ} (table : FinThinLoadTable n) (arc query : Fin n × Fin n)
    (value : ℕ) : (table.write arc value).read query = if query = arc then value else table.read query := by
  unfold FinThinLoadTable.read FinThinLoadTable.write
  simp only [Array.getElem_set]
  simp only [show (finThinLoadPosition arc).val = (finThinLoadPosition query).val ↔ query = arc from
    ⟨fun same => (finProdFinEquiv.injective (Fin.ext same)).symm,fun same => by subst query; rfl⟩]

private def FinThinLoadTable.bump {n : ℕ} (table : FinThinLoadTable n) (arc : Fin n × Fin n) :
    FinThinLoadTable n :=
  let index := finThinLoadPosition arc
  have fits : index.val < table.val.size := by rw [table.property]; exact index.isLt
  let amount := table.val[index.val]'fits
  ⟨table.val.set index.val (amount+1) fits,by simpa using table.property⟩

private def bumpFinThinLoadsOnList {n : ℕ} (table : FinThinLoadTable n) (cut : List (Fin n × Fin n))
    (work : ℕ) : FinThinLoadTable n × ℕ :=
  match cut with
  | [] => (table,work+2)
  | arc::rest =>
    let next := table.bump arc
    bumpFinThinLoadsOnList next rest (work+10)

private theorem bumpFinThinLoadsOnList_spec {n : ℕ} (table : FinThinLoadTable n) (cut : List (Fin n × Fin n))
    (work : ℕ) :
    let out := bumpFinThinLoadsOnList table cut work
    (∀ e, out.1.read e = table.read e+cut.count e) ∧ out.2 = work+10*cut.length+2 := by
  induction cut generalizing table work with
  | nil => simp [bumpFinThinLoadsOnList]
  | cons arc cut ih =>
    obtain ⟨same,meter⟩ := ih (table.write arc (table.read arc+1)) (work+10)
    refine ⟨?_,?_⟩
    · intro query
      rw [bumpFinThinLoadsOnList]
      change (bumpFinThinLoadsOnList (table.write arc (table.read arc+1)) cut (work+10)).1.read query = _
      rw [same,FinThinLoadTable.read_write,List.count_cons]
      by_cases eq : query = arc
      · subst query
        simp only [beq_self_eq_true, ite_true]
        omega
      · have different : arc ≠ query := Ne.symm eq
        simp [eq,different]
    · rw [bumpFinThinLoadsOnList]
      change (bumpFinThinLoadsOnList (table.write arc (table.read arc+1)) cut (work+10)).2 = _
      rw [meter,List.length_cons]
      omega

/-- Charge one table write and read per cut arc, using the numeric address. -/
def bumpFinThinLoadsWithWordWork {n : ℕ} (table : FinThinLoadTable n) (cut : List (Fin n × Fin n)) :
    FinThinLoadTable n × ℕ := bumpFinThinLoadsOnList table cut 2

private theorem bumpFinThinLoadsWithWordWork_count {n : ℕ} (table : FinThinLoadTable n)
    (cut : List (Fin n × Fin n)) :
    let out := bumpFinThinLoadsWithWordWork table cut
    (∀ e, out.1.read e = table.read e+cut.count e) ∧ out.2 = 10*cut.length+4 := by
  obtain ⟨same,work⟩ := bumpFinThinLoadsOnList_spec table cut 2
  exact ⟨same,work.trans (by omega)⟩

theorem bumpFinThinLoadsWithWordWork_spec {n : ℕ} (table : FinThinLoadTable n)
    (cut : List (Fin n × Fin n)) (unique : cut.Nodup) :
    let out := bumpFinThinLoadsWithWordWork table cut
    out.1.read = doubleCut cut.toFinset table.read ∧ out.2 = 10*cut.length+4 := by
  obtain ⟨same,work⟩ := bumpFinThinLoadsWithWordWork_count table cut
  refine ⟨?_,work⟩
  funext e
  rw [same,doubleCut]
  simp only [List.mem_toFinset]
  by_cases member : e ∈ cut
  · rw [List.count_eq_one_of_mem unique member, ite_eq_left member]
  · rw [List.count_eq_zero_of_not_mem member, Nat.add_zero, ite_eq_right member]

private theorem FinThinLoadTable.read_ext {n : ℕ} {a b : FinThinLoadTable n}
    (same : a.read = b.read) : a = b := by
  apply Subtype.ext
  refine Array.ext (a.property.trans b.property.symm) ?_
  intro i ai _
  let position : Fin (n*n) := ⟨i,a.property ▸ ai⟩
  let index : Fin n × Fin n := finProdFinEquiv.symm position
  have address : (finThinLoadPosition index).val = i :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply position)
  simpa only [FinThinLoadTable.read,address] using congrFun same index

private theorem bumpFinThinLoadsWithWordWork_perm {n : ℕ} (table : FinThinLoadTable n)
    (a b : List (Fin n × Fin n)) (permuted : a.Perm b) :
    bumpFinThinLoadsWithWordWork table a = bumpFinThinLoadsWithWordWork table b := by
  obtain ⟨first,workA⟩ := bumpFinThinLoadsWithWordWork_count table a
  obtain ⟨second,workB⟩ := bumpFinThinLoadsWithWordWork_count table b
  apply Prod.ext
  · apply FinThinLoadTable.read_ext
    funext e
    rw [first,second,permuted.count_eq e]
  · rw [workA,workB,permuted.length_eq]

/-- Update the array from the cut's stored list in one pass. Permuting that
list preserves its pointwise values and work. -/
def bumpFinThinLoadsOnCutWithWordWork {n : ℕ} (table : FinThinLoadTable n) (cut : Arcs (Fin n)) :
    FinThinLoadTable n × ℕ :=
  Quotient.lift (bumpFinThinLoadsWithWordWork table) (bumpFinThinLoadsWithWordWork_perm table) cut.val

theorem bumpFinThinLoadsOnCutWithWordWork_spec {n : ℕ} (table : FinThinLoadTable n) (cut : Arcs (Fin n)) :
    let out := bumpFinThinLoadsOnCutWithWordWork table cut
    out.1.read = doubleCut cut table.read ∧ out.2 = 10*cut.card+4 := by
  obtain ⟨values,nodup⟩ := cut
  revert nodup
  refine Quotient.inductionOn values ?_
  intro rows nodup
  have simple : rows.Nodup := by simpa using nodup
  have members : (⟨(rows : Multiset _),nodup⟩ : Arcs (Fin n)) = rows.toFinset := by
    ext e
    exact List.mem_toFinset.symm
  change (bumpFinThinLoadsWithWordWork table rows).1.read =
    doubleCut (⟨(rows : Multiset _),nodup⟩ : Arcs (Fin n)) table.read ∧
    (bumpFinThinLoadsWithWordWork table rows).2 = 10*rows.length+4
  rw [members]
  exact bumpFinThinLoadsWithWordWork_spec table rows simple

/-- Additional word allowance per call to the signed-flow thin separator. -/
def thinSeparatorArrayWordCap (n m : ℕ) : ℕ := 4 * (n*n) + m * (20*n+10) + 23

private abbrev ThinArraySeparator (n : ℕ) :=
  CutLoads (Fin n) → (Option (Finset (Fin n)) × ℕ) × ℕ

@[inline] private def thinCoverLoopWithArrayLoadWorkUsing {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (d : Fin n × Fin n) (findCut : ThinArraySeparator n) :
    ℕ → FinThinLoadTable n → (FinThinLoadTable n × ℕ) × ℕ × ℕ
  | 0, loads => ((loads,0),0,2)
  | fuel+1, loads =>
    let step := findCut loads.read
    match step.1.1 with
    | none => ((loads,0),step.1.2,step.2+4)
    | some W =>
      let cut := outgoingCut (intervalArcs G d) W
      let updated := bumpFinThinLoadsOnCutWithWordWork loads cut
      let rest := thinCoverLoopWithArrayLoadWorkUsing G m d findCut fuel updated.1
      ((rest.1.1,rest.1.2+1),step.1.2+(2*n*m+2*m)+rest.2.1,step.2+updated.2+rest.2.2+4)

private theorem thinCoverLoopWithArrayLoadWorkUsing_spec_of_invariant {n : ℕ}
    (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (d : Fin n × Fin n) (findCut : ThinArraySeparator n) (separatorCap : ℕ)
    (valid : FinThinLoadTable n → Prop)
    (exactCut : ∀ loads : FinThinLoadTable n, (findCut loads.read).1 = fastThinViolationWithSearchWork G d loads.read ∧
      (valid loads → (findCut loads.read).2 ≤ separatorCap))
    (closed : ∀ loads W, (findCut loads.read).1.1 = some W → valid loads →
      valid (bumpFinThinLoadsOnCutWithWordWork loads (outgoingCut (intervalArcs G d) W)).1)
    (fuel : ℕ) (loads : FinThinLoadTable n) :
    let out := thinCoverLoopWithArrayLoadWorkUsing G m d findCut fuel loads
    ((out.1.1.read,out.1.2),out.2.1) = thinCoverLoopWithSearchWork G d fuel loads.read ∧
      (valid loads → out.2.2 ≤ (out.1.2+1)*(10*m+8+separatorCap)) := by
  subst m
  induction fuel generalizing loads with
  | zero =>
    simp [thinCoverLoopWithArrayLoadWorkUsing,thinCoverLoopWithSearchWork]
    intro _
    omega
  | succ fuel ih =>
    let proposal := fastThinViolationWithSearchWork G d loads.read
    let step := findCut loads.read
    obtain ⟨sameCut, cutWork⟩ := exactCut loads
    change step.1 = proposal at sameCut
    change valid loads → step.2 ≤ separatorCap at cutWork
    cases separator : proposal.1 with
    | none =>
      change (fastThinViolationWithSearchWork G d loads.read).1 = none at separator
      simp only [thinCoverLoopWithArrayLoadWorkUsing,thinCoverLoopWithSearchWork,
        ← show step = findCut loads.read from rfl,sameCut,proposal,separator]
      simp only [Nat.zero_add,Nat.one_mul,true_and]
      intro h
      have work := cutWork h
      omega
    | some W =>
      change (fastThinViolationWithSearchWork G d loads.read).1 = some W at separator
      let cut := outgoingCut (intervalArcs G d) W
      let updated := bumpFinThinLoadsOnCutWithWordWork loads cut
      let rest := thinCoverLoopWithArrayLoadWorkUsing G G.card d findCut fuel updated.1
      obtain ⟨loadEq,loadWork⟩ := bumpFinThinLoadsOnCutWithWordWork_spec loads cut
      obtain ⟨tail,tailWork⟩ := ih updated.1
      change updated.1.read = doubleCut cut loads.read at loadEq
      change updated.2 = 10*cut.card+4 at loadWork
      rw [loadEq] at tail
      have inside : cut ⊆ G := (outgoingCut_subset _ _).trans (intervalArcs_subset _ _)
      simp only [thinCoverLoopWithArrayLoadWorkUsing,thinCoverLoopWithSearchWork,
        ← show step = findCut loads.read from rfl,sameCut,proposal,separator,Fintype.card_fin]
      change (((rest.1.1.read,rest.1.2+1),proposal.2+(2*n*G.card+2*G.card)+rest.2.1) = _) ∧ _
      rw [← tail]
      refine ⟨rfl,fun h => ?_⟩
      have found : step.1.1 = some W := (congrArg Prod.fst sameCut).trans separator
      have nextValid : valid updated.1 := closed loads W found h
      have nextWork := tailWork nextValid
      have limit : step.2+updated.2+4 ≤ 10*G.card+8+separatorCap := by
        have count := Finset.card_le_card inside
        have charged := cutWork h
        omega
      let B := 10*G.card+8+separatorCap
      change step.2+updated.2+rest.2.2+4 ≤ (rest.1.2+1+1)*B
      change rest.2.2 ≤ (rest.1.2+1)*B at nextWork
      calc
        _ = rest.2.2+(step.2+updated.2+4) := by omega
        _ ≤ (rest.1.2+1)*B+B := Nat.add_le_add nextWork limit
        _ = _ := by simp only [Nat.add_mul,Nat.one_mul]

private theorem thinCoverLoopWithArrayLoadWorkUsing_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (d : Fin n × Fin n) (findCut : ThinArraySeparator n) (separatorCap : ℕ)
    (exactCut : ∀ load, (findCut load).1 = fastThinViolationWithSearchWork G d load ∧ (findCut load).2 ≤ separatorCap)
    (fuel : ℕ) (loads : FinThinLoadTable n) :
    let out := thinCoverLoopWithArrayLoadWorkUsing G m d findCut fuel loads
    ((out.1.1.read,out.1.2),out.2.1) = thinCoverLoopWithSearchWork G d fuel loads.read ∧
      out.2.2 ≤ (out.1.2+1)*(10*m+8+separatorCap) := by
  obtain ⟨record,work⟩ := thinCoverLoopWithArrayLoadWorkUsing_spec_of_invariant G m hm d findCut separatorCap
    (fun _ => True) (fun load => ⟨(exactCut load.read).1,fun _ => (exactCut load.read).2⟩)
    (fun _ _ _ _ => trivial) fuel loads
  exact ⟨record,work trivial⟩

/-- Follow the existing separator decisions with the load function backed by a
current array. Preserve the existing search count and separately charge updates. -/
def thinCoverLoopWithArrayLoadWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (d : Fin n × Fin n) :
    ℕ → FinThinLoadTable n → (FinThinLoadTable n × ℕ) × ℕ × ℕ
  | 0, loads => ((loads,0),0,2)
  | fuel+1, loads =>
    let step := fastThinViolationWithSearchWork G d loads.read
    match step.1 with
    | none => ((loads,0),step.2,4)
    | some W =>
      let cut := outgoingCut (intervalArcs G d) W
      let updated := bumpFinThinLoadsOnCutWithWordWork loads cut
      let rest := thinCoverLoopWithArrayLoadWork G m d fuel updated.1
      ((rest.1.1,rest.1.2+1),step.2+(2*n*m+2*m)+rest.2.1,updated.2+rest.2.2+4)

private theorem thinCoverLoopWithArrayLoadWorkUsing_zero {n : ℕ} (G : Arcs (Fin n))
    (m : ℕ) (d : Fin n × Fin n) (fuel : ℕ) (loads : FinThinLoadTable n) :
    thinCoverLoopWithArrayLoadWorkUsing G m d (fun load => (fastThinViolationWithSearchWork G d load,0)) fuel loads =
      thinCoverLoopWithArrayLoadWork G m d fuel loads := by
  induction fuel generalizing loads with
  | zero => rfl
  | succ fuel ih =>
    simp only [thinCoverLoopWithArrayLoadWorkUsing,thinCoverLoopWithArrayLoadWork,Nat.zero_add]
    split
    · rfl
    · rw [ih]

theorem thinCoverLoopWithArrayLoadWork_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (d : Fin n × Fin n) (fuel : ℕ) (loads : FinThinLoadTable n) :
    let out := thinCoverLoopWithArrayLoadWork G m d fuel loads
    ((out.1.1.read,out.1.2),out.2.1) = thinCoverLoopWithSearchWork G d fuel loads.read ∧
      out.2.2 ≤ (out.1.2+1)*(10*m+8) := by
  simpa only [thinCoverLoopWithArrayLoadWorkUsing_zero,Nat.add_zero] using
    thinCoverLoopWithArrayLoadWorkUsing_spec G m hm d (fun load => (fastThinViolationWithSearchWork G d load,0))
      0 (fun _ => ⟨rfl,le_rfl⟩) fuel loads

/-- Keep the same decisions and measure indexed residual-flow updates too. -/
def thinCoverLoopWithArraySeparatorWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (d : Fin n × Fin n)
    (fuel : ℕ) (loads : FinThinLoadTable n) : (FinThinLoadTable n × ℕ) × ℕ × ℕ :=
  thinCoverLoopWithArrayLoadWorkUsing G m d (fastThinViolationWithDenseFlowWork G d m) fuel loads

theorem thinCoverLoopWithArraySeparatorWork_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (d : Fin n × Fin n) (fuel : ℕ) (loads : FinThinLoadTable n) :
    let out := thinCoverLoopWithArraySeparatorWork G m d fuel loads
    ((out.1.1.read,out.1.2),out.2.1) = thinCoverLoopWithSearchWork G d fuel loads.read ∧
      out.2.2 ≤ (out.1.2+1)*(10*m+8+thinSeparatorArrayWordCap n m) :=
  thinCoverLoopWithArrayLoadWorkUsing_spec G m hm d (fastThinViolationWithDenseFlowWork G d m)
    (thinSeparatorArrayWordCap n m) (fastThinViolationWithDenseFlowWork_spec G d m hm) fuel loads

/-- Additional preparation, indexed residual scans and signed updates in a thin separator. -/
def thinIndexedTablesWordCap (n m : ℕ) : ℕ :=
  15*(n*n)+m*(20*n+10+6+4*(m.log2+1)+13)+(m+2)*(16*(n*n)+4)+43

def thinCoverLoopWithIndexedTablesWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (d : Fin n × Fin n)
    (fuel : ℕ) (loads : FinThinLoadTable n) : (FinThinLoadTable n × ℕ) × ℕ × ℕ :=
  thinCoverLoopWithArrayLoadWorkUsing G m d
    (fun load => fastThinViolationWithIndexedTablesWork G d m (fun e => (load e,6))) fuel loads

theorem thinCoverLoopWithIndexedTablesWork_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (d : Fin n × Fin n) (fuel : ℕ) (loads : FinThinLoadTable n) :
    let out := thinCoverLoopWithIndexedTablesWork G m d fuel loads
    ((out.1.1.read,out.1.2),out.2.1) = thinCoverLoopWithSearchWork G d fuel loads.read ∧
      (Reach G d.1 d.2 → (∀ e ∈ G, loads.read e ≤ m.log2+1) →
        out.2.2 ≤ (out.1.2+1)*(10*m+8+thinIndexedTablesWordCap n m)) := by
  subst m
  let m := G.card
  let findCut : ThinArraySeparator n := fun load => fastThinViolationWithIndexedTablesWork G d m (fun e => (load e,6))
  let valid := fun snapshot : FinThinLoadTable n => Reach G d.1 d.2 ∧ ∀ e ∈ G, snapshot.read e ≤ m.log2+1
  have exactCut (snapshot : FinThinLoadTable n) : (findCut snapshot.read).1 = fastThinViolationWithSearchWork G d snapshot.read ∧
      (valid snapshot → (findCut snapshot.read).2 ≤ thinIndexedTablesWordCap n m) := by
    have c := fastThinViolationWithIndexedTablesWork_spec G d m rfl (fun e => (snapshot.read e,6)) (m.log2+1) 6
    exact ⟨c.1,fun h => c.2 (fun e he => ⟨h.2 e he,le_rfl⟩)⟩
  have closed (snapshot : FinThinLoadTable n) (W : Finset (Fin n))
      (found : (findCut snapshot.read).1.1 = some W) (h : valid snapshot) :
      valid (bumpFinThinLoadsOnCutWithWordWork snapshot (outgoingCut (intervalArcs G d) W)).1 := by
    let cut := outgoingCut (intervalArcs G d) W
    have output : fastThinViolation G d snapshot.read = some W :=
      (fastThinViolationWithSearchWork_spec G d snapshot.read).1.symm.trans
        ((congrArg Prod.fst (exactCut snapshot).1).symm.trans found)
    have small : cutMass cut snapshot.read < m := (fastThinViolation_some h.1 output).2.2
    have updated := (bumpFinThinLoadsOnCutWithWordWork_spec snapshot cut).1
    exact ⟨h.1,updated ▸ doubleCut_bounded small h.2⟩
  obtain ⟨record,work⟩ := thinCoverLoopWithArrayLoadWorkUsing_spec_of_invariant G m rfl d findCut
    (thinIndexedTablesWordCap n m) valid exactCut closed fuel loads
  exact ⟨record,fun reach cap => work ⟨reach,cap⟩⟩

private theorem thinCoverRunWithSearchWorkFrom_append {n : ℕ} (G : Arcs (Fin n))
    (P D : List (Fin n × Fin n)) (loads : CutLoads (Fin n)) :
    let first := thinCoverRunWithSearchWorkFrom G P loads
    let rest := thinCoverRunWithSearchWorkFrom G D first.1.1
    thinCoverRunWithSearchWorkFrom G (P++D) loads =
      ((rest.1.1,first.1.2+rest.1.2),first.2+rest.2) := by
  induction P generalizing loads with
  | nil => simp [thinCoverRunWithSearchWorkFrom]
  | cons d P ih =>
    let step := thinCoverLoopWithSearchWork G d (G.card*(G.card.log2+1)+1) loads
    dsimp only [List.cons_append,thinCoverRunWithSearchWorkFrom]
    rw [ih step.1.1]
    simp [step,Nat.add_assoc]

/-- Advance the fractional loads and their accumulated base tally by one
request. The old evaluator's complete-prefix record has the same data. -/
theorem thinCoverRunWithSearchWork_append_one {n : ℕ} (G : Arcs (Fin n))
    (D : List (Fin n × Fin n)) (d : Fin n × Fin n) :
    let first := thinCoverRunWithSearchWork G D
    let step := thinCoverLoopWithSearchWork G d (G.card*(G.card.log2+1)+1) first.1.1
    thinCoverRunWithSearchWork G (D++[d]) =
      ((step.1.1,first.1.2+step.1.2),first.2+step.2) := by
  have same := thinCoverRunWithSearchWorkFrom_append G D [d] (fun _ => 0)
  simpa [thinCoverRunWithSearchWork,thinCoverRunWithSearchWorkFrom] using same

private def zeroFinLoadArrayLoop : ℕ → Array ℕ → ℕ → Array ℕ × ℕ
  | 0, values, work => (values,work+2)
  | remaining+1, values, work => zeroFinLoadArrayLoop remaining (values.push 0) (work+4)

private theorem zeroFinLoadArrayLoop_spec (k : ℕ) (values : Array ℕ) (work : ℕ) :
    let out := zeroFinLoadArrayLoop k values work
    out.1.toList = values.toList ++ List.replicate k 0 ∧ out.2 = work+4*k+2 := by
  induction k generalizing values work with
  | zero => simp [zeroFinLoadArrayLoop]
  | succ k ih =>
    simp only [zeroFinLoadArrayLoop]
    obtain ⟨stored,meter⟩ := ih (values.push 0) (work+4)
    exact ⟨by simp only [stored,Array.toList_push,List.replicate_succ,List.append_assoc,List.singleton_append],
      meter.trans (by omega)⟩

/-- Reserve the dense array once and initialize one slot per possible pair
of vertex labels, charging the explicit loop and slot construction. -/
def emptyFinThinLoadsWithWordWork (n : ℕ) : FinThinLoadTable n × ℕ :=
  let size := n*n
  let out := zeroFinLoadArrayLoop size (Array.emptyWithCapacity size) 3
  have stored : out.1.toList = List.replicate size 0 :=
    (zeroFinLoadArrayLoop_spec size (Array.emptyWithCapacity size) 3).1.trans rfl
  have count := congrArg List.length stored
  (⟨out.1,by simpa only [Array.length_toList,List.length_replicate] using count⟩,out.2)

theorem emptyFinThinLoadsWithWordWork_spec (n : ℕ) :
    let out := emptyFinThinLoadsWithWordWork n
    out.1 = emptyFinThinLoads n ∧ out.2 = 4*(n*n)+5 := by
  have result := zeroFinLoadArrayLoop_spec (n*n) (Array.emptyWithCapacity (n*n)) 3
  refine ⟨?_,result.2.trans (by omega)⟩
  apply Subtype.ext
  apply Array.toList_inj.mp
  change (zeroFinLoadArrayLoop (n*n) (Array.emptyWithCapacity (n*n)) 3).1.toList = (Array.replicate (n*n) 0).toList
  simpa using result.1

/-- State kept between thin requests when the same fractional trace is reused
across its own prefixes. -/
structure FinThinPrefixState (n : ℕ) where
  loads : FinThinLoadTable n
  updates : ℕ
  searchWork : ℕ
  updateWork : ℕ

def FinThinPrefixState.fractionalRecord {n : ℕ} (state : FinThinPrefixState n) :
    (CutLoads (Fin n) × ℕ) × ℕ := ((state.loads.read,state.updates),state.searchWork)

def FinThinPrefixState.initial (n : ℕ) : FinThinPrefixState n :=
  let prepared := emptyFinThinLoadsWithWordWork n
  ⟨prepared.1,0,0,prepared.2⟩

@[inline] private def thinCoverArrayPrefixStepUsing {n : ℕ} (old : FinThinPrefixState n)
    (evaluate : FinThinLoadTable n → (FinThinLoadTable n × ℕ) × ℕ × ℕ) : FinThinPrefixState n :=
  let next := evaluate old.loads
  ⟨next.1.1,old.updates+next.1.2,old.searchWork+next.2.1,old.updateWork+next.2.2+3⟩

private theorem thinCoverArrayPrefixStepUsing_eq {n : ℕ} (G : Arcs (Fin n))
    (old : FinThinPrefixState n) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (earlier : old.fractionalRecord = thinCoverRunWithSearchWork G D)
    (evaluate : FinThinLoadTable n → (FinThinLoadTable n × ℕ) × ℕ × ℕ)
    (same : let step := evaluate old.loads
      ((step.1.1.read,step.1.2),step.2.1) =
        thinCoverLoopWithSearchWork G d (G.card*(G.card.log2+1)+1) old.loads.read) :
    (thinCoverArrayPrefixStepUsing old evaluate).fractionalRecord = thinCoverRunWithSearchWork G (D++[d]) := by
  let fuel := G.card*(G.card.log2+1)+1
  have appendEq := thinCoverRunWithSearchWork_append_one G D d
  change thinCoverRunWithSearchWork G (D++[d]) = _ at appendEq
  rw [← earlier] at appendEq
  change thinCoverRunWithSearchWork G (D++[d]) =
    let next := thinCoverLoopWithSearchWork G d fuel old.loads.read
    ((next.1.1,old.updates+next.1.2),old.searchWork+next.2) at appendEq
  rw [← same] at appendEq
  exact appendEq.symm

private theorem thinCoverArrayPrefixStepUsing_spec {n : ℕ} (G : Arcs (Fin n))
    (old : FinThinPrefixState n) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (earlier : old.fractionalRecord = thinCoverRunWithSearchWork G D)
    (evaluate : FinThinLoadTable n → (FinThinLoadTable n × ℕ) × ℕ × ℕ) (B : ℕ)
    (exactStep : let step := evaluate old.loads
      ((step.1.1.read,step.1.2),step.2.1) =
        thinCoverLoopWithSearchWork G d (G.card*(G.card.log2+1)+1) old.loads.read ∧
      step.2.2 ≤ (step.1.2+1)*B) :
    let next := thinCoverArrayPrefixStepUsing old evaluate
    next.fractionalRecord = thinCoverRunWithSearchWork G (D++[d]) ∧
      next.updateWork ≤ old.updateWork+(next.updates-old.updates+1)*B+3 := by
  let step := evaluate old.loads
  obtain ⟨same,work⟩ := exactStep
  refine ⟨thinCoverArrayPrefixStepUsing_eq G old D d earlier evaluate same,?_⟩
  change old.updateWork+step.2.2+3 ≤ old.updateWork+(old.updates+step.1.2-old.updates+1)*B+3
  rw [Nat.add_sub_cancel_left]
  exact Nat.add_le_add_right (Nat.add_le_add_left work _) _

def thinCoverArrayPrefixStep {n : ℕ} (G : Arcs (Fin n)) (m fuel : ℕ)
    (old : FinThinPrefixState n) (d : Fin n × Fin n) : FinThinPrefixState n :=
  thinCoverArrayPrefixStepUsing old (thinCoverLoopWithArrayLoadWork G m d fuel)

theorem thinCoverArrayPrefixStep_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (old : FinThinPrefixState n) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (earlier : old.fractionalRecord = thinCoverRunWithSearchWork G D) :
    let next := thinCoverArrayPrefixStep G m (m*(m.log2+1)+1) old d
    next.fractionalRecord = thinCoverRunWithSearchWork G (D++[d]) ∧
      next.updateWork ≤ old.updateWork+(next.updates-old.updates+1)*(10*m+8)+3 := by
  subst m
  let fuel := G.card*(G.card.log2+1)+1
  exact thinCoverArrayPrefixStepUsing_spec G old D d earlier (thinCoverLoopWithArrayLoadWork G G.card d fuel)
    (10*G.card+8) (thinCoverLoopWithArrayLoadWork_spec G G.card rfl d fuel old.loads)

def thinCoverArrayPrefixStepWithSeparatorWork {n : ℕ} (G : Arcs (Fin n)) (m fuel : ℕ)
    (old : FinThinPrefixState n) (d : Fin n × Fin n) : FinThinPrefixState n :=
  thinCoverArrayPrefixStepUsing old (thinCoverLoopWithArraySeparatorWork G m d fuel)

theorem thinCoverArrayPrefixStepWithSeparatorWork_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (old : FinThinPrefixState n) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (earlier : old.fractionalRecord = thinCoverRunWithSearchWork G D) :
    let next := thinCoverArrayPrefixStepWithSeparatorWork G m (m*(m.log2+1)+1) old d
    next.fractionalRecord = thinCoverRunWithSearchWork G (D++[d]) ∧
      next.updateWork ≤ old.updateWork+(next.updates-old.updates+1)*(10*m+8+thinSeparatorArrayWordCap n m)+3 := by
  subst m
  let fuel := G.card*(G.card.log2+1)+1
  exact thinCoverArrayPrefixStepUsing_spec G old D d earlier (thinCoverLoopWithArraySeparatorWork G G.card d fuel)
    (10*G.card+8+thinSeparatorArrayWordCap n G.card) (thinCoverLoopWithArraySeparatorWork_spec G G.card rfl d fuel old.loads)

def thinCoverArrayPrefixStepWithIndexedTablesWork {n : ℕ} (G : Arcs (Fin n)) (m fuel : ℕ)
    (old : FinThinPrefixState n) (d : Fin n × Fin n) : FinThinPrefixState n :=
  thinCoverArrayPrefixStepUsing old (thinCoverLoopWithIndexedTablesWork G m d fuel)

theorem thinCoverArrayPrefixStepWithIndexedTablesWork_eq {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (old : FinThinPrefixState n) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (earlier : old.fractionalRecord = thinCoverRunWithSearchWork G D) :
    (thinCoverArrayPrefixStepWithIndexedTablesWork G m (m*(m.log2+1)+1) old d).fractionalRecord =
      thinCoverRunWithSearchWork G (D++[d]) := by
  subst m
  let fuel := G.card*(G.card.log2+1)+1
  exact thinCoverArrayPrefixStepUsing_eq G old D d earlier (thinCoverLoopWithIndexedTablesWork G G.card d fuel)
    (thinCoverLoopWithIndexedTablesWork_spec G G.card rfl d fuel old.loads).1

theorem thinCoverArrayPrefixStepWithIndexedTablesWork_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (old : FinThinPrefixState n) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (feasible : ∀ q ∈ D++[d], Reach G q.1 q.2) (earlier : old.fractionalRecord = thinCoverRunWithSearchWork G D) :
    let next := thinCoverArrayPrefixStepWithIndexedTablesWork G m (m*(m.log2+1)+1) old d
    next.fractionalRecord = thinCoverRunWithSearchWork G (D++[d]) ∧
      next.updateWork ≤ old.updateWork+(next.updates-old.updates+1)*(10*m+8+thinIndexedTablesWordCap n m)+3 := by
  subst m
  let fuel := G.card*(G.card.log2+1)+1
  have head := feasible d (List.mem_append_right _ (List.mem_singleton_self _))
  have projected := congrArg (fun r : (CutLoads (Fin n) × ℕ) × ℕ => r.1.1) earlier
  have cap : ∀ e ∈ G, old.loads.read e ≤ G.card.log2+1 := by
    change old.loads.read = (thinCoverRunWithSearchWork G D).1.1 at projected
    rw [projected]
    exact (thinCoverRunWithSearchWork_spec G D (fun q h => feasible q (List.mem_append_left _ h))).2.1
  obtain ⟨same,work⟩ := thinCoverLoopWithIndexedTablesWork_spec G G.card rfl d fuel old.loads
  exact thinCoverArrayPrefixStepUsing_spec G old D d earlier (thinCoverLoopWithIndexedTablesWork G G.card d fuel)
    (10*G.card+8+thinIndexedTablesWordCap n G.card) ⟨same,work head cap⟩

/-- Advance the same load table once per arrival in the thin trace. -/
def thinCoverArrayPrefixFold {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (D : List (Fin n × Fin n)) :
    FinThinPrefixState n :=
  let fuel := m*(m.log2+1)+1
  D.foldl (thinCoverArrayPrefixStep G m fuel) (FinThinPrefixState.initial n)

private theorem thinCoverArrayPrefixFoldUsing_spec {n : ℕ} (G : Arcs (Fin n)) (B : ℕ)
    (advance : FinThinPrefixState n → (Fin n × Fin n) → FinThinPrefixState n)
    (valid : (Fin n × Fin n) → Prop)
    (exactStep : ∀ prior P d, (∀ q ∈ P++[d], valid q) → prior.fractionalRecord = thinCoverRunWithSearchWork G P →
      let next := advance prior d
      next.fractionalRecord = thinCoverRunWithSearchWork G (P++[d]) ∧
        next.updateWork ≤ prior.updateWork+(next.updates-prior.updates+1)*B+3)
    (D : List (Fin n × Fin n)) (feasible : ∀ q ∈ D, valid q) :
    let out := D.foldl advance (FinThinPrefixState.initial n)
    out.fractionalRecord = thinCoverRunWithSearchWork G D ∧
      out.updateWork ≤ (out.updates+D.length)*B+3*D.length+(4*(n*n)+5) := by
  induction D using List.reverseRecOn with
  | nil =>
    have blank : (emptyFinThinLoads n).read = fun _ => 0 := funext emptyFinThinLoads_read
    simp [FinThinPrefixState.initial,FinThinPrefixState.fractionalRecord,
      thinCoverRunWithSearchWork,thinCoverRunWithSearchWorkFrom,blank,
      (emptyFinThinLoadsWithWordWork_spec n).1,(emptyFinThinLoadsWithWordWork_spec n).2]
  | append_singleton D d ih =>
    let prior := D.foldl advance (FinThinPrefixState.initial n)
    let advanced := advance prior d
    obtain ⟨same,oldWork⟩ := ih (fun q h => feasible q (List.mem_append_left _ h))
    let initialCost := 4*(n*n)+5
    change prior.updateWork ≤ (prior.updates+D.length)*B+3*D.length+initialCost at oldWork
    obtain ⟨next,newWork⟩ := exactStep prior D d feasible same
    have output : (D++[d]).foldl advance (FinThinPrefixState.initial n) = advanced := by
      rw [List.foldl_append]
      rfl
    dsimp only
    rw [output]
    refine ⟨next,?_⟩
    have updates : prior.updates ≤ advanced.updates := by
      have oldCount := congrArg (fun r : (CutLoads (Fin n) × ℕ) × ℕ => r.1.2) same
      have nextCount := congrArg (fun r : (CutLoads (Fin n) × ℕ) × ℕ => r.1.2) next
      have appendCount := congrArg (fun r : (CutLoads (Fin n) × ℕ) × ℕ => r.1.2)
        (thinCoverRunWithSearchWork_append_one G D d)
      change prior.updates = (thinCoverRunWithSearchWork G D).1.2 at oldCount
      change advanced.updates = (thinCoverRunWithSearchWork G (D++[d])).1.2 at nextCount
      change (thinCoverRunWithSearchWork G (D++[d])).1.2 = (thinCoverRunWithSearchWork G D).1.2+_ at appendCount
      exact oldCount.le.trans (Nat.le_add_right _ _) |>.trans_eq (nextCount.trans appendCount).symm
    have total : prior.updates+D.length+(advanced.updates-prior.updates+1) =
        advanced.updates+(D++[d]).length := by
      simp only [List.length_append,List.length_singleton]
      omega
    change advanced.updateWork ≤ (advanced.updates+(D++[d]).length)*B+3*(D++[d]).length+initialCost
    calc
      _ ≤ prior.updateWork+(advanced.updates-prior.updates+1)*B+3 := newWork
      _ ≤ (prior.updates+D.length)*B+3*D.length+initialCost+(advanced.updates-prior.updates+1)*B+3 :=
        Nat.add_le_add_right (Nat.add_le_add_right oldWork _) _
      _ = (prior.updates+D.length+(advanced.updates-prior.updates+1))*B+3*(D.length+1)+initialCost := by ring
      _ = _ := by rw [total,List.length_append,List.length_singleton]

theorem thinCoverArrayPrefixFold_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (D : List (Fin n × Fin n)) :
    let out := thinCoverArrayPrefixFold G m D
    out.fractionalRecord = thinCoverRunWithSearchWork G D ∧
      out.updateWork ≤ (out.updates+D.length)*(10*m+8)+3*D.length+(4*(n*n)+5) :=
  thinCoverArrayPrefixFoldUsing_spec G (10*m+8) (thinCoverArrayPrefixStep G m (m*(m.log2+1)+1))
    (fun _ => True) (fun prior P d _ => thinCoverArrayPrefixStep_spec G m hm prior P d) D (fun _ _ => trivial)

def thinCoverArrayPrefixFoldWithSeparatorWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (D : List (Fin n × Fin n)) : FinThinPrefixState n :=
  let fuel := m*(m.log2+1)+1
  D.foldl (thinCoverArrayPrefixStepWithSeparatorWork G m fuel) (FinThinPrefixState.initial n)

theorem thinCoverArrayPrefixFoldWithSeparatorWork_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (D : List (Fin n × Fin n)) :
    let out := thinCoverArrayPrefixFoldWithSeparatorWork G m D
    out.fractionalRecord = thinCoverRunWithSearchWork G D ∧
      out.updateWork ≤ (out.updates+D.length)*(10*m+8+thinSeparatorArrayWordCap n m)+3*D.length+(4*(n*n)+5) :=
  thinCoverArrayPrefixFoldUsing_spec G (10*m+8+thinSeparatorArrayWordCap n m)
    (thinCoverArrayPrefixStepWithSeparatorWork G m (m*(m.log2+1)+1))
    (fun _ => True) (fun prior P d _ => thinCoverArrayPrefixStepWithSeparatorWork_spec G m hm prior P d)
    D (fun _ _ => trivial)

def thinCoverArrayPrefixFoldWithIndexedTablesWork {n : ℕ} (G : Arcs (Fin n)) (m : ℕ)
    (D : List (Fin n × Fin n)) : FinThinPrefixState n :=
  let fuel := m*(m.log2+1)+1
  D.foldl (thinCoverArrayPrefixStepWithIndexedTablesWork G m fuel) (FinThinPrefixState.initial n)

theorem thinCoverArrayPrefixFoldWithIndexedTablesWork_spec {n : ℕ} (G : Arcs (Fin n)) (m : ℕ) (hm : m = G.card)
    (D : List (Fin n × Fin n)) (feasible : ∀ q ∈ D, Reach G q.1 q.2) :
    let out := thinCoverArrayPrefixFoldWithIndexedTablesWork G m D
    out.fractionalRecord = thinCoverRunWithSearchWork G D ∧
      out.updateWork ≤ (out.updates+D.length)*(10*m+8+thinIndexedTablesWordCap n m)+3*D.length+(4*(n*n)+5) :=
  thinCoverArrayPrefixFoldUsing_spec G (10*m+8+thinIndexedTablesWordCap n m)
    (thinCoverArrayPrefixStepWithIndexedTablesWork G m (m*(m.log2+1)+1)) (fun q => Reach G q.1 q.2)
    (thinCoverArrayPrefixStepWithIndexedTablesWork_spec G m hm) D feasible

end OnlineReachabilityPreservers
