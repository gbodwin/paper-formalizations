import OnlineReachabilityPreservers.LocalRegularization
import OnlineReachabilityPreservers.OppositePathChains

/-! Split full-bridge-free path systems through size four by mirroring cuts between opposite intersections. -/

namespace OnlineReachabilityPreservers

open Finset

section CutSynchronization

variable {B : Type*} [DecidableEq B]

private def cutMate (partner : B → Option B) (a : B) : Finset B :=
  (partner a).elim ∅ fun b => {b}

omit [DecidableEq B] in
private theorem mem_cutMate (partner : B → Option B) {a b : B} :
    b ∈ cutMate partner a ↔ partner a = some b := by
  unfold cutMate
  cases partner a <;> simp [eq_comm]

/-- Add the counterpart of every selected boundary that has one. -/
def synchronizedCuts (selected : Finset B) (partner : B → Option B) : Finset B :=
  selected ∪ selected.biUnion (cutMate partner)

theorem synchronizedCuts_card (selected : Finset B) (partner : B → Option B) :
    (synchronizedCuts selected partner).card ≤ 2 * selected.card := by
  have extra : (selected.biUnion (cutMate partner)).card ≤ selected.card := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _ ∈ selected, 1 := sum_le_sum fun a _ => by
        unfold cutMate
        cases partner a <;> simp
      _ = _ := by simp
  exact (card_union_le _ _).trans (by omega)

theorem synchronizedCuts_mem_iff (selected : Finset B) (partner : B → Option B)
    (flip : ∀ {a b}, partner a = some b → partner b = some a)
    {a b : B} (paired : partner a = some b) :
    a ∈ synchronizedCuts selected partner ↔ b ∈ synchronizedCuts selected partner := by
  have forward {a b : B} (ab : partner a = some b) (inside : a ∈ synchronizedCuts selected partner) :
      b ∈ synchronizedCuts selected partner := by
    rcases mem_union.mp inside with h | h
    · exact mem_union_right _ (mem_biUnion.mpr ⟨a, h, (mem_cutMate partner).mpr ab⟩)
    · obtain ⟨c,hc,ca⟩ := mem_biUnion.mp h
      have ac := flip ((mem_cutMate partner).mp ca)
      have eq := Option.some.inj (ac.symm.trans ab)
      exact mem_union_left _ (eq ▸ hc)
  exact ⟨forward paired, forward (flip paired)⟩

end CutSynchronization

section Blocks

variable {I : Type*} [DecidableEq I] (len : I → ℕ)

/-- Number the blocks by how many cut positions precede each rank. -/
def rankBlock (cuts : Finset (Σ i, Fin (len i))) (i : I) (r : Fin (len i)) : ℕ :=
  (cuts.filter fun c => c.1 = i ∧ c.2.val < r.val).card

theorem rankBlock_mono (cuts : Finset (Σ i, Fin (len i))) (i : I) :
    Monotone (rankBlock len cuts i) := by
  intro r s le
  apply card_le_card
  intro a ha
  obtain ⟨inside, row, earlier⟩ := mem_filter.mp ha
  exact mem_filter.mpr ⟨inside, row, earlier.trans_le le⟩

theorem rankBlock_lt_of_cut {cuts : Finset (Σ i, Fin (len i))} {i : I} {r c s : Fin (len i)}
    (rc : r ≤ c) (cs : c < s) (inside : ⟨i,c⟩ ∈ cuts) :
    rankBlock len cuts i r < rankBlock len cuts i s := by
  apply card_lt_card
  have sub : cuts.filter (fun x => x.1 = i ∧ x.2.val < r.val) ⊆
      cuts.filter (fun x => x.1 = i ∧ x.2.val < s.val) := by
    intro a ha
    obtain ⟨mem, row, less⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem,row, less.trans (lt_of_le_of_lt rc cs)⟩
  have h : (⟨i,c⟩ : Σ j, Fin (len j)) ∈ cuts.filter (fun x => x.1 = i ∧ x.2.val < s.val) :=
    mem_filter.mpr ⟨inside,rfl,cs⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun eq => (not_lt_of_ge rc) (mem_filter.mp (eq.symm ▸ h)).2.2⟩

theorem rankBlock_adjacent_same_iff {cuts : Finset (Σ i, Fin (len i))} {i : I} {r s : Fin (len i)}
    (successor : s.val = r.val + 1) :
    rankBlock len cuts i r = rankBlock len cuts i s ↔ ⟨i,r⟩ ∉ cuts := by
  constructor
  · intro equal hit
    have rs : r < s := by change r.val < s.val; omega
    exact (rankBlock_lt_of_cut len le_rfl rs hit).ne equal
  · intro noCut
    unfold rankBlock
    congr 1
    ext c
    simp only [mem_filter]
    constructor
    · rintro ⟨inSet, row, less⟩
      exact ⟨inSet, row, by omega⟩
    · rintro ⟨inSet, row, less⟩
      refine ⟨inSet, row, ?_⟩
      by_contra! ge
      have eq : c.2.val = r.val := by omega
      obtain ⟨j, t⟩ := c
      change j = i at row
      subst j
      have te : t = r := Fin.ext eq
      subst t
      exact noCut inSet


variable [Fintype I]

/-- Break a rank order into consecutive blocks of width `width`. The final position has no cut. -/
def baseRankCuts (width : ℕ) : Finset (Σ i, Fin (len i)) :=
  univ.filter fun c => (c.2.val + 1) % width = 0 ∧ c.2.val + 1 < len c.1

omit [DecidableEq I] in
theorem baseRankCuts_card {width : ℕ} (positive : 0 < width) :
    (baseRankCuts len width).card ≤ (∑ i, len i) / width := by
  classical
  let position (c : (baseRankCuts len width : Finset (Σ i, Fin (len i)))) :
      Σ i, Fin (len i / width) := by
    let q := (c.val.2.val + 1) / width
    have cut := (mem_filter.mp c.property).2
    have factor : width * q = c.val.2.val + 1 := by
      have h := Nat.mod_add_div (c.val.2.val + 1) width
      rw [cut.1, zero_add] at h
      exact h
    have nonzero : 0 < q := by
      by_contra! none
      have eq : q = 0 := Nat.eq_zero_of_le_zero none
      rw [eq, Nat.mul_zero] at factor
      omega
    have upper : q ≤ len c.val.1 / width := Nat.div_le_div_right cut.2.le
    exact ⟨c.val.1, ⟨q - 1, (Nat.sub_lt nonzero (by decide)).trans_le upper⟩⟩
  have injection : Function.Injective position := by
    rintro ⟨⟨i,r⟩,hr⟩ ⟨⟨j,s⟩,hs⟩ eq
    have keys := congrArg Sigma.fst eq
    change i = j at keys
    subst j
    have slot := congrArg (fun c : Σ i, Fin (len i / width) => c.2.val) eq
    change (r.val+1)/width - 1 = (s.val+1)/width - 1 at slot
    have rMod := (mem_filter.mp hr).2.1
    have sMod := (mem_filter.mp hs).2.1
    have rFactor := Nat.mod_add_div (r.val + 1) width
    have sFactor := Nat.mod_add_div (s.val + 1) width
    change (r.val+1)%width = 0 at rMod
    change (s.val+1)%width = 0 at sMod
    rw [rMod, zero_add] at rFactor
    rw [sMod, zero_add] at sFactor
    have posR : 0 < (r.val+1)/width := by
      by_contra! z
      rw [Nat.eq_zero_of_le_zero z, Nat.mul_zero] at rFactor
      omega
    have posS : 0 < (s.val+1)/width := by
      by_contra! z
      rw [Nat.eq_zero_of_le_zero z, Nat.mul_zero] at sFactor
      omega
    have quotient : (r.val+1)/width = (s.val+1)/width := by omega
    rw [quotient] at rFactor
    have valEq : r.val = s.val := by omega
    exact Subtype.ext (congrArg (Sigma.mk i) (Fin.ext valEq))
  have count := Fintype.card_le_of_injective _ injection
  rw [Fintype.card_coe, Fintype.card_sigma] at count
  simp only [Fintype.card_fin] at count
  apply count.trans
  apply (Nat.le_div_iff_mul_le positive).mpr
  rw [sum_mul]
  exact sum_le_sum fun i _ => Nat.div_mul_le_self (len i) width

theorem quotient_eq_of_same_rankBlock {width : ℕ} (positive : 0 < width)
    {cuts : Finset (Σ i, Fin (len i))} (included : baseRankCuts len width ⊆ cuts)
    {i : I} {r s : Fin (len i)} (order : r ≤ s)
    (same : rankBlock len cuts i r = rankBlock len cuts i s) : r.val / width = s.val / width := by
  have nondecreasing : r.val / width ≤ s.val / width := Nat.div_le_div_right order
  by_contra different
  have increment : r.val / width + 1 ≤ s.val / width := by omega
  let boundary := (r.val / width + 1) * width
  have low : r.val < boundary := by
    simpa [boundary, Nat.mul_comm] using Nat.lt_mul_div_succ r.val positive
  have high : boundary ≤ s.val := (Nat.le_div_iff_mul_le positive).mp increment
  let c : Fin (len i) := ⟨boundary - 1, lt_of_le_of_lt (Nat.sub_le _ _) (high.trans_lt s.isLt)⟩
  have base : (⟨i,c⟩ : Σ j, Fin (len j)) ∈ baseRankCuts len width := by
    have boundaryEq : c.val + 1 = boundary := by change boundary-1+1 = boundary; omega
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change (c.val + 1) % width = 0 ∧ c.val + 1 < len i
    rw [boundaryEq]
    exact ⟨Nat.mul_mod_left _ _, high.trans_lt s.isLt⟩
  have contrary := rankBlock_lt_of_cut len (i := i) (c := c) (r := r) (s := s)
    (by change r.val ≤ boundary - 1; omega) (by change boundary - 1 < s.val; omega) (included base)
  exact contrary.ne same

end Blocks

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

variable {V I : Type*} [DecidableEq V] [LinearOrder I]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The new path block for an incidence. Values off the path are unused. -/
def packedPathBlock {paths : I → List V} (indexes : PackedPathRanks paths)
    (cuts : Finset (PackedBoundary paths)) (i : I) (x : V) : ℕ :=
  if inside : x ∈ paths i then rankBlock (fun j => (paths j).length) cuts i (indexes.rank i ⟨x,inside⟩) else 0

private theorem packedPathBlock_mem {paths : I → List V} (indexes : PackedPathRanks paths)
    (cuts : Finset (PackedBoundary paths)) {i : I} {x : V} (inside : x ∈ paths i) :
    packedPathBlock indexes cuts i x = rankBlock (fun j => (paths j).length) cuts i (indexes.rank i ⟨x,inside⟩) := by
  rw [packedPathBlock, dite_eq_left inside]

private theorem oppositeNeighbor_blocks {paths : I → List V} (indexes : PackedPathRanks paths)
    (free : BridgeFree (ListBefore paths) 3) (selected : Finset (PackedBoundary paths))
    {a b : I} {x y : V} (adjacent : OppositeNeighbors paths a b x y) :
    let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
    let block := packedPathBlock indexes cuts
    block a x ≤ block a y ∧ block b y ≤ block b x ∧ (block a x = block a y ↔ block b y = block b x) := by
  let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
  have reverse := oppositeNeighbors_swap free adjacent
  have first := indexes.adjacent adjacent
  have second := indexes.adjacent reverse
  let xA := indexes.rank a ⟨x,adjacent.2.1.1⟩
  let yA := indexes.rank a ⟨y,adjacent.2.1.2.1⟩
  let yB := indexes.rank b ⟨y,adjacent.2.2.1.1⟩
  let xB := indexes.rank b ⟨x,adjacent.2.2.1.2.1⟩
  have firstOrder : xA ≤ yA := by change xA.val ≤ yA.val; change yA.val = xA.val + 1 at first; omega
  have secondOrder : yB ≤ xB := by change yB.val ≤ xB.val; change xB.val = yB.val + 1 at second; omega
  have matchCut : oppositeCutPartner indexes ⟨a,xA⟩ = some ⟨b,yB⟩ :=
    (oppositeCutPartner_eq indexes free).mpr ⟨x,y,adjacent,rfl,rfl⟩
  have mirror {u v : PackedBoundary paths} (h : oppositeCutPartner indexes u = some v) :
      oppositeCutPartner indexes v = some u :=
    (oppositeCutPartner_eq indexes free).mpr ((oppositeCutPartner_eq indexes free).mp h |>.swap indexes free)
  have bothCut := synchronizedCuts_mem_iff selected (oppositeCutPartner indexes) mirror matchCut
  dsimp only
  rw [packedPathBlock_mem indexes cuts adjacent.2.1.1, packedPathBlock_mem indexes cuts adjacent.2.1.2.1,
    packedPathBlock_mem indexes cuts adjacent.2.2.1.1, packedPathBlock_mem indexes cuts adjacent.2.2.1.2.1]
  refine ⟨rankBlock_mono _ cuts _ firstOrder, rankBlock_mono _ cuts _ secondOrder, ?_⟩
  let len (i : I) := (paths i).length
  have left := rankBlock_adjacent_same_iff len (cuts := cuts) (i := a) (r := xA) (s := yA) first
  have right := rankBlock_adjacent_same_iff len (cuts := cuts) (i := b) (r := yB) (s := xB) second
  exact left.trans ((not_congr bothCut).trans right.symm)

/-- Two oppositely shared vertices are separated on one path precisely when
separated on the other. Every cut across their common interval is mirrored. -/
theorem oppositePath_blocks_eq_iff {paths : I → List V} (indexes : PackedPathRanks paths)
    (free : BridgeFree (ListBefore paths) 3) (selected : Finset (PackedBoundary paths))
    {a b : I} (apart : a ≠ b) {x y : V}
    (xy : ListBefore paths a x y) (yx : ListBefore paths b y x) :
    let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
    let block := packedPathBlock indexes cuts
    block a x = block a y ↔ block b y = block b x := by
  let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
  let block := packedPathBlock indexes cuts
  have steps : ∀ {u v}, Relation.TransGen (OppositeNeighbors paths a b) u v →
      block a u ≤ block a v ∧ block b v ≤ block b u ∧ (block a u = block a v ↔ block b v = block b u) := by
    intro u v track
    induction track with
    | single adjacent => exact oppositeNeighbor_blocks indexes free selected adjacent
    | @tail v w _ adjacent ih =>
      obtain ⟨monoA, monoB, same⟩ := ih
      obtain ⟨followsA, followsB, also⟩ := oppositeNeighbor_blocks indexes free selected adjacent
      change block a v ≤ block a w at followsA
      change block b w ≤ block b v at followsB
      change block a v = block a w ↔ block b w = block b v at also
      refine ⟨monoA.trans followsA, followsB.trans monoB, ?_⟩
      constructor
      · intro eq
        exact (also.mp (by omega)).trans (same.mp (by omega))
      · intro eq
        exact (same.mpr (by omega)).trans (also.mpr (by omega))
  exact (steps (oppositeNeighbors_connect free apart xy yx)).2.2

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

variable {V I : Type*} [DecidableEq V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

abbrev PackedBlockIndex {paths : I → List V} (cuts : Finset (PackedBoundary paths)) :=
  Σₗ i : I, Fin ((cuts.filter fun p => p.fst = i).card + 1)

/-- Filter the original order into the blocks of the synchronized rank order. -/
def packedPathPiece {paths : I → List V} (indexes : PackedPathRanks paths)
    (cuts : Finset (PackedBoundary paths)) (j : PackedBlockIndex cuts) : List V :=
  (paths j.fst).filter fun x => decide (packedPathBlock indexes cuts j.fst x = j.snd.val)

omit [Fintype I] in
theorem mem_packedPathPiece {paths : I → List V} (indexes : PackedPathRanks paths)
    (cuts : Finset (PackedBoundary paths)) (j : PackedBlockIndex cuts) (x : V) :
    x ∈ packedPathPiece indexes cuts j ↔ x ∈ paths j.fst ∧ packedPathBlock indexes cuts j.fst x = j.snd.val := by
  simp [packedPathPiece]

omit [Fintype I] in
theorem packedPathPiece_simple {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (indexes : PackedPathRanks paths) (cuts : Finset (PackedBoundary paths)) (j : PackedBlockIndex cuts) :
    (packedPathPiece indexes cuts j).Nodup := List.filter_sublist.nodup (simple j.fst)

omit [Fintype I] in
private theorem packedPathBlock_bound {paths : I → List V} (indexes : PackedPathRanks paths)
    (cuts : Finset (PackedBoundary paths)) {i : I} {x : V} (inside : x ∈ paths i) :
    packedPathBlock indexes cuts i x < (cuts.filter fun p => p.fst = i).card + 1 := by
  rw [packedPathBlock_mem indexes cuts inside]
  apply Nat.lt_succ_of_le
  apply card_le_card
  intro a h
  obtain ⟨present,row,_⟩ := mem_filter.mp h
  exact mem_filter.mpr ⟨present,row⟩

omit [DecidableEq V] in
theorem packedBlockIndex_card {paths : I → List V} (cuts : Finset (PackedBoundary paths)) :
    Fintype.card (PackedBlockIndex cuts) = Fintype.card I + cuts.card := by
  rw [Fintype.card_lex, Fintype.card_sigma]
  simp only [Fintype.card_fin, sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one]
  have fibers := card_eq_sum_card_fiberwise (s := cuts) (t := (univ : Finset I)) (f := Sigma.fst) (by simp)
  rw [← fibers, add_comm]

omit [Fintype I] in
private theorem packedPathPiece_disjoint {paths : I → List V} (indexes : PackedPathRanks paths)
    (cuts : Finset (PackedBoundary paths)) {j k : PackedBlockIndex cuts} (same : j.fst = k.fst)
    {x : V} (hj : x ∈ packedPathPiece indexes cuts j) (hk : x ∈ packedPathPiece indexes cuts k) : j = k := by
  obtain ⟨a,r⟩ := j
  obtain ⟨b,s⟩ := k
  change a = b at same
  subst b
  have equal := (mem_packedPathPiece indexes cuts _ _).mp hj |>.2
  have equal' := (mem_packedPathPiece indexes cuts _ _).mp hk |>.2
  have same : r.val = s.val := equal.symm.trans equal'
  exact congrArg (Sigma.mk a) (Fin.ext same)

omit [Fintype I] in
theorem packedPathPiece_fullFree_short {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    {size : ℕ} (three : 3 ≤ size) (five : size ≤ 5)
    (indexes : PackedPathRanks paths) (free : BridgeFree (ListBefore paths) size)
    (selected : Finset (PackedBoundary paths)) :
    let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
    BridgeFree (ListBefore (packedPathPiece indexes cuts)) size := by
  let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
  let pieces := packedPathPiece indexes cuts
  let parent (j : PackedBlockIndex cuts) := j.fst
  have step {j : PackedBlockIndex cuts} {x y : V} (xy : ListBefore pieces j x y) :
      ListBefore paths (parent j) x y :=
    listBefore_of_sublist (paths := fun k : PackedBlockIndex cuts => paths (parent k)) (cut := pieces)
      (simple j.fst) List.filter_sublist xy
  have freeThree : BridgeFree (ListBefore paths) 3 := fun _ hk => free (hk.trans three)
  change BridgeFree (ListBefore pieces) size
  intro k hk
  refine ⟨fun b => (free hk).false ?_⟩
  refine listBridge_after_opposite_safe_split_through_five (paths := paths) (pieces := pieces) parent
    (fun {i _ _} h => step (j := i) h)
    (fun {_ _ _} different same x y => different (packedPathPiece_disjoint indexes cuts same x y))
    (fun _ {_ _ _ _} different x y => no_parallel_list_steps free.halfFree (by omega) different x y)
    ?_ (by omega) b
  intro _ j j' q x y same apart xy yx hx hy
  have bx := (mem_packedPathPiece indexes cuts j x).mp hx |>.2
  have by' := (mem_packedPathPiece indexes cuts j' y).mp hy |>.2
  have cy := (mem_packedPathPiece indexes cuts q y).mp yx.1 |>.2
  have cx := (mem_packedPathPiece indexes cuts q x).mp yx.2.1 |>.2
  have synced := (oppositePath_blocks_eq_iff indexes freeThree selected apart xy (step yx)).mpr (cy.trans cx.symm)
  obtain ⟨i,s⟩ := j
  obtain ⟨i',t⟩ := j'
  change i = i' at same
  subst i'
  exact congrArg (Sigma.mk i) (Fin.ext (bx.symm.trans (synced.trans by')))

omit [Fintype I] in
theorem packedPathPiece_fullFree {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (indexes : PackedPathRanks paths) (free : BridgeFree (ListBefore paths) 4)
    (selected : Finset (PackedBoundary paths)) :
    let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
    BridgeFree (ListBefore (packedPathPiece indexes cuts)) 4 :=
  packedPathPiece_fullFree_short simple (by decide) (by decide) indexes free selected

omit [Fintype I] in
private theorem packedPathPiece_sum_at {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (indexes : PackedPathRanks paths) (cuts : Finset (PackedBoundary paths)) (i : I) :
    (∑ r : Fin ((cuts.filter fun p => p.fst = i).card + 1), (packedPathPiece indexes cuts ⟨i,r⟩).length) =
      (paths i).length := by
  let width := (cuts.filter fun p => p.fst = i).card + 1
  let block := packedPathBlock indexes cuts i
  let row := paths i
  have covers : ∀ x ∈ row.toFinset, block x ∈ range width := by
    intro x hx
    exact mem_range.mpr (packedPathBlock_bound indexes cuts (List.mem_toFinset.mp hx))
  have count := card_eq_sum_card_fiberwise (s := row.toFinset) (t := range width) (f := block) covers
  have same (q : ℕ) : (row.toFinset.filter (fun x => block x = q)).card =
      (row.filter (fun x => decide (block x = q))).length := by
    rw [← List.toFinset_card_of_nodup (List.filter_sublist.nodup (simple i))]
    congr 1
    ext x
    simp [mem_filter, row]
  calc
    _ = ∑ q ∈ range width, (row.filter (fun x => decide (block x = q))).length :=
      Fin.sum_univ_eq_sum_range _ _
    _ = row.toFinset.card := by
      rw [count]
      exact sum_congr rfl fun q _ => (same q).symm
    _ = _ := List.toFinset_card_of_nodup (simple i)

theorem packedPathPiece_sum {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (indexes : PackedPathRanks paths) (cuts : Finset (PackedBoundary paths)) :
    (∑ j : PackedBlockIndex cuts, (packedPathPiece indexes cuts j).length) = ∑ i, (paths i).length := by
  change (∑ j : (Σ i : I, Fin ((cuts.filter fun p => p.fst = i).card + 1)),
    (packedPathPiece indexes cuts j).length) = _
  rw [Fintype.sum_sigma]
  exact sum_congr rfl fun i _ => packedPathPiece_sum_at simple indexes cuts i


/-- Synchronized boundaries refine the initial width blocks. -/
theorem packedPathPiece_length {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (indexes : PackedPathRanks paths) (cuts : Finset (PackedBoundary paths)) (j : PackedBlockIndex cuts)
    {width : ℕ} (widthPos : 0 < width)
    (containsBase : baseRankCuts (fun i => (paths i).length) width ⊆ cuts) :
    (packedPathPiece indexes cuts j).length ≤ width := by
  let piece := (packedPathPiece indexes cuts j).toFinset
  have notes (x : piece) : x.val ∈ paths j.fst ∧ packedPathBlock indexes cuts j.fst x.val = j.snd.val :=
    (mem_packedPathPiece indexes cuts j x.val).mp (List.mem_toFinset.mp x.property)
  let rank (x : piece) := indexes.rank j.fst ⟨x.val,(notes x).1⟩
  let slot (x : piece) : Fin width := ⟨(rank x).val % width, Nat.mod_lt _ widthPos⟩
  have inject : Function.Injective slot := by
    intro x y equal
    have one := (notes x).2
    have two := (notes y).2
    rw [packedPathBlock_mem indexes cuts (notes x).1] at one
    rw [packedPathBlock_mem indexes cuts (notes y).1] at two
    have same := one.trans two.symm
    have block : (rank x).val / width = (rank y).val / width := by
      rcases le_total (rank x) (rank y) with le | ge
      · exact quotient_eq_of_same_rankBlock _ widthPos containsBase le same
      · exact (quotient_eq_of_same_rankBlock _ widthPos containsBase ge same.symm).symm
    have residue := congrArg Fin.val equal
    change (rank x).val % width = (rank y).val % width at residue
    have recoverX := Nat.mod_add_div (rank x).val width
    have recoverY := Nat.mod_add_div (rank y).val width
    rw [block, residue] at recoverX
    have ranksEq : rank x = rank y := Fin.ext (recoverX.symm.trans recoverY)
    have vals := congrArg (fun t : {v : V // v ∈ paths j.fst} => t.val) ((indexes.rank j.fst).injective ranksEq)
    exact Subtype.ext vals
  have count := Fintype.card_le_of_injective slot inject
  rwa [Fintype.card_coe, Fintype.card_fin, List.toFinset_card_of_nodup (packedPathPiece_simple simple indexes cuts j)] at count

/-- Each new incidence maps to a different original incidence at its vertex. -/
theorem packedPathPiece_degree_le {paths : I → List V} (indexes : PackedPathRanks paths)
    (cuts : Finset (PackedBoundary paths)) (v : V) :
    (occurrences (fun j => (packedPathPiece indexes cuts j).toFinset) v).card ≤
      (occurrences (fun i => (paths i).toFinset) v).card := by
  let marks (j : PackedBlockIndex cuts) := (packedPathPiece indexes cuts j).toFinset
  have on {j : PackedBlockIndex cuts} (hj : j ∈ occurrences marks v) : v ∈ packedPathPiece indexes cuts j :=
    List.mem_toFinset.mp ((mem_occurrences (marks := marks)).mp hj)
  apply card_le_card_of_injOn (fun j => j.fst)
  · intro j hj
    exact (mem_occurrences (marks := fun i => (paths i).toFinset)).mpr
      (List.mem_toFinset.mpr ((mem_packedPathPiece indexes cuts j v).mp (on hj)).1)
  · intro j hj k hk equal
    exact packedPathPiece_disjoint indexes cuts equal (on hj) (on hk)

end OnlineReachabilityPreservers
