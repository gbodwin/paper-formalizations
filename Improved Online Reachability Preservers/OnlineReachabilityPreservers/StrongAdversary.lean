import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import OnlineReachabilityPreservers.Basic

/-! The changing-graph adversary of Theorem 3 and its lattice construction. -/

namespace OnlineReachabilityPreservers

open Finset

abbrev LayerGrid (steps rows : ℕ) := Fin (steps + 1) × Fin rows

/-- The first coordinate is the slope and the second coordinate is the starting row. -/
abbrev LatticeLine (slopes starts : ℕ) := Fin slopes ×ₗ Fin starts

variable {steps rows slopes starts : ℕ}

/-- The row boundary for all line vertices, including the last layer. -/
def LatticeFits (steps rows slopes starts : ℕ) : Prop :=
  starts + steps * (slopes - 1) ≤ rows

def latticeVertex (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) (j : Fin (steps + 1)) : LayerGrid steps rows :=
  (j, ⟨(ofLex line).2.val + j.val * (ofLex line).1.val, by
    have hj : j.val ≤ steps := by omega
    have hw : (ofLex line).1.val ≤ slopes - 1 := by omega
    have ha := (ofLex line).2.isLt
    have hm := Nat.mul_le_mul hj hw
    unfold LatticeFits at fits
    omega⟩)

def latticeEdge (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) (j : Fin steps) :
    LayerGrid steps rows × LayerGrid steps rows :=
  (latticeVertex fits line j.castSucc, latticeVertex fits line j.succ)

def latticePath (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) : Arcs (LayerGrid steps rows) :=
  univ.image (latticeEdge fits line)

def latticePair (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) : LayerGrid steps rows × LayerGrid steps rows :=
  (latticeVertex fits line 0, latticeVertex fits line (Fin.last steps))

private theorem latticePath_reach (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) (j : Fin (steps + 1)) :
    Reach (latticePath fits line) (latticeVertex fits line 0) (latticeVertex fits line j) := by
  induction j using Fin.induction with
  | zero => exact .refl
  | succ j ih => exact ih.tail (mem_image.mpr ⟨j, mem_univ _, rfl⟩)

private theorem reaches_layer_and_row {G : Arcs (LayerGrid steps rows)} (slope : ℕ)
    (bounded : ∀ ⦃u v⦄, Edge G u v → v.1.val = u.1.val + 1 ∧ v.2.val ≤ u.2.val + slope)
    {u v : LayerGrid steps rows} (reach : Reach G u v) :
    u.1.val ≤ v.1.val ∧ v.2.val + u.1.val * slope ≤ u.2.val + v.1.val * slope := by
  induction reach with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | @tail v w _ edge ih =>
    obtain ⟨layer, row⟩ := bounded edge
    constructor
    · omega
    · rw [layer, Nat.add_mul, Nat.one_mul]
      omega

private theorem lineStep_forced (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) {G : Arcs (LayerGrid steps rows)}
    (bounded : ∀ ⦃u v⦄, Edge G u v →
      v.1.val = u.1.val + 1 ∧ v.2.val ≤ u.2.val + (ofLex line).1.val)
    {u v : LayerGrid steps rows} (reach : Reach G u v)
    (start : u = latticeVertex fits line u.1) (finish : v = latticeVertex fits line v.1)
    (j : Fin steps) (left : u.1.val ≤ j.val) (right : j.val < v.1.val) :
    latticeEdge fits line j ∈ G := by
  induction reach with
  | refl => omega
  | @tail v w reach edge ih =>
    obtain ⟨layer, row⟩ := bounded edge
    obtain ⟨_, progress⟩ := reaches_layer_and_row (ofLex line).1.val bounded reach
    have startHeight := congrArg (fun z : LayerGrid steps rows => z.2.val) start
    have endHeight := congrArg (fun z : LayerGrid steps rows => z.2.val) finish
    change u.2.val = (ofLex line).2.val + u.1.val * (ofLex line).1.val at startHeight
    change w.2.val = (ofLex line).2.val + w.1.val * (ofLex line).1.val at endHeight
    rw [layer, Nat.add_mul, Nat.one_mul] at endHeight
    have middleHeight : v.2.val = (ofLex line).2.val + v.1.val * (ofLex line).1.val := by
      omega
    have middle : v = latticeVertex fits line v.1 := by
      exact Prod.ext rfl (Fin.ext middleHeight)
    by_cases before : j.val < v.1.val
    · exact ih middle before
    · have jv : v.1 = j.castSucc := Fin.ext (by change v.1.val = j.val; omega)
      have jw : w.1 = j.succ := Fin.ext (by rw [layer, jv]; rfl)
      rw [middle, finish, jv, jw] at edge
      exact edge

private theorem latticeEdge_properties (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) (j : Fin steps) :
    (latticeEdge fits line j).2.1.val = (latticeEdge fits line j).1.1.val + 1 ∧
      (latticeEdge fits line j).2.2.val =
        (latticeEdge fits line j).1.2.val + (ofLex line).1.val := by
  constructor
  · rfl
  · change (ofLex line).2.val + (j.val + 1) * (ofLex line).1.val =
      (ofLex line).2.val + j.val * (ofLex line).1.val + (ofLex line).1.val
    rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- If only lines of at most the demand slope have been revealed, all its edges are mandatory. -/
theorem latticePath_forced (fits : LatticeFits steps rows slopes starts)
    (line : LatticeLine slopes starts) (revealed : Finset (LatticeLine slopes starts))
    (slopes_le : ∀ q ∈ revealed, (ofLex q).1 ≤ (ofLex line).1)
    {B : Arcs (LayerGrid steps rows)}
    (available : B ⊆ revealed.biUnion (latticePath fits))
    (served : Reach B (latticePair fits line).1 (latticePair fits line).2) :
    latticePath fits line ⊆ B := by
  have bounded : ∀ ⦃u v⦄, Edge B u v →
      v.1.val = u.1.val + 1 ∧ v.2.val ≤ u.2.val + (ofLex line).1.val := by
    intro u v edge
    obtain ⟨q,hq,edgeQ⟩ := mem_biUnion.mp (available edge)
    obtain ⟨j,_,heq⟩ := mem_image.mp edgeQ
    have ⟨layer,row⟩ := latticeEdge_properties fits q j
    rw [heq] at layer row
    exact ⟨layer, row.le.trans (Nat.add_le_add_left (slopes_le q hq) _)⟩
  intro e he
  obtain ⟨j,_,rfl⟩ := mem_image.mp he
  exact lineStep_forced fits line bounded served rfl rfl j (Nat.zero_le _) j.isLt

private theorem latticeEdge_injective (fits : LatticeFits steps rows slopes starts) :
    Function.Injective (fun q : LatticeLine slopes starts × Fin steps =>
      latticeEdge fits q.1 q.2) := by
  intro x y eq
  have layer := congrArg (fun e : LayerGrid steps rows × LayerGrid steps rows => e.1.1.val) eq
  have left := congrArg (fun e : LayerGrid steps rows × LayerGrid steps rows => e.1.2.val) eq
  have right := congrArg (fun e : LayerGrid steps rows × LayerGrid steps rows => e.2.2.val) eq
  have hx := (latticeEdge_properties fits x.1 x.2).2
  have hy := (latticeEdge_properties fits y.1 y.2).2
  change x.2.val = y.2.val at layer
  change (latticeEdge fits x.1 x.2).1.2.val = (latticeEdge fits y.1 y.2).1.2.val at left
  change (latticeEdge fits x.1 x.2).2.2.val = (latticeEdge fits y.1 y.2).2.2.val at right
  have slope : (ofLex x.1).1.val = (ofLex y.1).1.val := by omega
  change (ofLex x.1).2.val + x.2.val * (ofLex x.1).1.val =
    (ofLex y.1).2.val + y.2.val * (ofLex y.1).1.val at left
  rw [layer,slope] at left
  exact Prod.ext (ofLex.injective (Prod.ext (Fin.ext slope) (Fin.ext (Nat.add_right_cancel left))))
    (Fin.ext layer)

theorem lattice_union_card (fits : LatticeFits steps rows slopes starts)
    (lines : Finset (LatticeLine slopes starts)) :
    (lines.biUnion (latticePath fits)).card = lines.card * steps := by
  have eq : lines.biUnion (latticePath fits) =
      (lines ×ˢ (univ : Finset (Fin steps))).image (fun q => latticeEdge fits q.1 q.2) := by
    ext e
    simp [latticePath, Prod.exists]
  rw [eq, card_image_of_injective _ (latticeEdge_injective fits), card_product]
  simp

section InsertionGame

variable {V : Type*} [DecidableEq V]

/-- One round reveals its new available arcs before asking for reachability. -/
structure InsertionRequest (V : Type*) where
  added : Arcs V
  pair : V × V

def insertedArcs (requests : List (InsertionRequest V)) (count : ℕ) : Arcs V :=
  ((requests.take count).map InsertionRequest.added).toFinset.biUnion id

theorem mem_insertedArcs {requests : List (InsertionRequest V)} {count : ℕ} {e : V × V} :
    e ∈ insertedArcs requests count ↔ ∃ r ∈ requests.take count, e ∈ r.added := by
  simp [insertedArcs, -List.map_take]

theorem insertedArcs_mono (requests : List (InsertionRequest V)) : Monotone (insertedArcs requests) := by
  intro i j hij e he
  obtain ⟨r, hr, h⟩ := mem_insertedArcs.mp he
  exact mem_insertedArcs.mpr ⟨r, List.take_subset_take_left requests hij hr, h⟩

theorem insertedArcs_contains (requests : List (InsertionRequest V)) (i : Fin requests.length) :
    (requests.get i).added ⊆ insertedArcs requests (i.val + 1) := by
  intro e he
  refine mem_insertedArcs.mpr ⟨requests.get i, List.mem_take_iff_getElem.mpr ?_, he⟩
  exact ⟨i.val, lt_min (Nat.lt_succ_self _) i.isLt, rfl⟩

/-- The builder starts empty, purchases irrevocably, and may use only arcs
available by this round. Each request must be served immediately. -/
structure InsertionBuilder (requests : List (InsertionRequest V)) (bought : ℕ → Arcs V) : Prop where
  empty : bought 0 = ∅
  monotone : Monotone bought
  available : ∀ i : Fin requests.length, bought (i.val + 1) ⊆ insertedArcs requests (i.val + 1)
  served : ∀ i : Fin requests.length,
    Reach (bought (i.val + 1)) (requests.get i).pair.1 (requests.get i).pair.2

/-- All requests are feasible in the graph available when they arrive. -/
def InsertionFeasible (requests : List (InsertionRequest V)) : Prop :=
  ∀ i : Fin requests.length,
    Reach (insertedArcs requests (i.val + 1)) (requests.get i).pair.1 (requests.get i).pair.2

theorem insertionFeasible_builder {requests : List (InsertionRequest V)}
    (feasible : InsertionFeasible requests) : InsertionBuilder requests (insertedArcs requests) :=
  ⟨by simp [insertedArcs], insertedArcs_mono requests, fun _ => Subset.rfl, feasible⟩

end InsertionGame

def latticeRounds (fits : LatticeFits steps rows slopes starts)
    (lines : Finset (LatticeLine slopes starts)) : List (InsertionRequest (LayerGrid steps rows)) :=
  (lines.sort (· ≤ ·)).map fun line => ⟨latticePath fits line, latticePair fits line⟩

theorem latticeRounds_length (fits : LatticeFits steps rows slopes starts)
    (lines : Finset (LatticeLine slopes starts)) : (latticeRounds fits lines).length = lines.card := by
  simp [latticeRounds]

private theorem latticeRounds_get (fits : LatticeFits steps rows slopes starts)
    (lines : Finset (LatticeLine slopes starts)) (i : Fin (latticeRounds fits lines).length) :
    (latticeRounds fits lines).get i =
      let line := (lines.sort (· ≤ ·))[i.val]'(by simpa [latticeRounds] using i.isLt)
      ⟨latticePath fits line, latticePair fits line⟩ := by
  change ((lines.sort (· ≤ ·)).map
    (fun line => InsertionRequest.mk (latticePath fits line) (latticePair fits line)))[i.val] = _
  rw [List.getElem_map]

theorem latticeRounds_feasible (fits : LatticeFits steps rows slopes starts)
    (lines : Finset (LatticeLine slopes starts)) : InsertionFeasible (latticeRounds fits lines) := by
  intro i
  have h := insertedArcs_contains (latticeRounds fits lines) i
  rw [latticeRounds_get] at h ⊢
  exact reach_mono h (latticePath_reach fits _ (Fin.last steps))

private theorem latticePair_injective (fits : LatticeFits steps rows slopes starts)
    (positive : 0 < steps) : Function.Injective (latticePair fits) := by
  intro a b eq
  have left := congrArg (fun e : LayerGrid steps rows × LayerGrid steps rows => e.1.2.val) eq
  simp only [latticePair, latticeVertex, Fin.val_zero, Nat.zero_mul, Nat.add_zero] at left
  have right := congrArg (fun e : LayerGrid steps rows × LayerGrid steps rows => e.2.2.val) eq
  change (ofLex a).2.val + steps * (ofLex a).1.val =
    (ofLex b).2.val + steps * (ofLex b).1.val at right
  rw [left] at right
  exact ofLex.injective (Prod.ext
    (Fin.ext (Nat.eq_of_mul_eq_mul_left positive (Nat.add_left_cancel right))) (Fin.ext left))

theorem latticeRounds_distinct (fits : LatticeFits steps rows slopes starts)
    (positive : 0 < steps) (lines : Finset (LatticeLine slopes starts)) :
    ((latticeRounds fits lines).map InsertionRequest.pair).Nodup := by
  simpa [latticeRounds, Function.comp_def] using
    (Finset.sort_nodup (s := lines) (· ≤ ·)).map (latticePair_injective fits positive)

/-- Inserting the chosen lines in nondecreasing slope order forces every
builder to purchase all their distinct arcs. -/
theorem theorem3_lattice_lower (fits : LatticeFits steps rows slopes starts)
    (lines : Finset (LatticeLine slopes starts)) {bought : ℕ → Arcs (LayerGrid steps rows)}
    (legal : InsertionBuilder (latticeRounds fits lines) bought) :
    lines.card * steps ≤ (bought lines.card).card := by
  rw [← lattice_union_card fits lines]
  apply card_le_card
  intro e he
  obtain ⟨line, hline, he⟩ := mem_biUnion.mp he
  have present : line ∈ lines.sort (· ≤ ·) := (Finset.mem_sort _).mpr hline
  obtain ⟨j, get⟩ := List.mem_iff_get.mp present
  let i : Fin (latticeRounds fits lines).length := ⟨j.val, by
    simpa [latticeRounds] using j.isLt⟩
  have request : (latticeRounds fits lines).get i =
      ⟨latticePath fits line, latticePair fits line⟩ := by
    rw [latticeRounds_get]
    change InsertionRequest.mk (latticePath fits ((lines.sort (· ≤ ·)).get j))
      (latticePair fits ((lines.sort (· ≤ ·)).get j)) = _
    rw [get]
  have served : Reach (bought (j.val + 1)) (latticePair fits line).1 (latticePair fits line).2 := by
    simpa only [request] using legal.served i
  let preceding := lines.filter fun q => q ≤ line
  have available : bought (j.val + 1) ⊆ preceding.biUnion (latticePath fits) := by
    intro f hf
    obtain ⟨r, hr, had⟩ := mem_insertedArcs.mp (legal.available i hf)
    have hr' : r ∈ ((lines.sort (· ≤ ·)).take (j.val + 1)).map
        (fun q => InsertionRequest.mk (latticePath fits q) (latticePair fits q)) := by
      simpa [latticeRounds, List.map_take] using hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨k, hk, eq⟩ := List.mem_take_iff_getElem.mp hq
    let k' : Fin (lines.sort (· ≤ ·)).length := ⟨k, (lt_min_iff.mp hk).2⟩
    have equal : (lines.sort (· ≤ ·)).get k' = q := eq
    have prior : k' ≤ j := Nat.lt_succ_iff.mp (lt_min_iff.mp hk).1
    have ord := (Finset.pairwise_sort (s := lines) (· ≤ ·)).rel_get_of_le prior
    have qle : q ≤ line := equal ▸ get ▸ ord
    have qmem : q ∈ lines := (Finset.mem_sort _).mp (List.take_subset _ _ hq)
    exact mem_biUnion.mpr ⟨q, mem_filter.mpr ⟨qmem, qle⟩, had⟩
  have forced := latticePath_forced fits line preceding
    (fun _ hq => Prod.Lex.monotone_fst_ofLex (mem_filter.mp hq).2) available served
  have within : j.val + 1 ≤ lines.card := by
    simpa using j.isLt
  exact legal.monotone within (forced he)

section Relabel

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

private def InsertionRequest.relabel (f : V ↪ W) (r : InsertionRequest V) : InsertionRequest W :=
  ⟨r.added.map (f.prodMap f), (f.prodMap f) r.pair⟩

private theorem insertedArcs_relabel (f : V ↪ W) (requests : List (InsertionRequest V)) (i : ℕ) :
    insertedArcs (requests.map (InsertionRequest.relabel f)) i =
      (insertedArcs requests i).map (f.prodMap f) := by
  ext e
  simp only [mem_insertedArcs, ← List.map_take, List.mem_map, mem_map]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
    obtain ⟨a, ha, eq⟩ := mem_map.mp h
    exact ⟨a, ⟨r, hr, ha⟩, eq⟩
  · rintro ⟨a, ⟨r, hr, ha⟩, eq⟩
    exact ⟨r.relabel f, ⟨r, hr, rfl⟩, mem_map.mpr ⟨a, ha, eq⟩⟩

omit [DecidableEq V] [DecidableEq W] in
private theorem reach_relabel {G : Arcs V} (f : V ↪ W) {a b : V} :
    Reach (G.map (f.prodMap f)) (f a) (f b) ↔ Reach G a b := by
  constructor
  · have recover (w : W) (reach : Reach (G.map (f.prodMap f)) (f a) w) :
        ∃ v, f v = w ∧ Reach G a v := by
      induction reach with
      | refl => exact ⟨a, rfl, .refl⟩
      | @tail z y _ edge ih =>
        obtain ⟨v, eq, path⟩ := ih
        obtain ⟨e, member, same⟩ := mem_map.mp edge
        have first : e.1 = v := f.injective ((congrArg Prod.fst same).trans eq.symm)
        exact ⟨e.2, congrArg Prod.snd same, path.tail (by rwa [← first])⟩
    intro path
    obtain ⟨v, eq, h⟩ := recover (f b) path
    exact f.injective eq ▸ h
  · intro path
    induction path with
    | refl => exact .refl
    | tail _ edge ih => exact ih.tail (mem_map_of_mem _ edge)

omit [DecidableEq V] [DecidableEq W] in
private theorem relabel_get (f : V ↪ W) (requests : List (InsertionRequest V))
    (i : Fin (requests.map (InsertionRequest.relabel f)).length) :
    (requests.map (InsertionRequest.relabel f)).get i =
      (requests.get ⟨i.val, by simpa using i.isLt⟩).relabel f := by
  rw [List.get_eq_getElem, List.getElem_map]
  rfl

private theorem relabel_feasible (f : V ↪ W) {requests : List (InsertionRequest V)}
    (h : InsertionFeasible requests) : InsertionFeasible (requests.map (InsertionRequest.relabel f)) := by
  intro i
  rw [insertedArcs_relabel, relabel_get]
  exact (reach_relabel f).mpr (h ⟨i.val, by simpa using i.isLt⟩)

omit [DecidableEq V] [DecidableEq W] in
private theorem relabel_distinct (f : V ↪ W) {requests : List (InsertionRequest V)}
    (distinct : (requests.map InsertionRequest.pair).Nodup) :
    ((requests.map (InsertionRequest.relabel f)).map InsertionRequest.pair).Nodup := by
  simpa [List.map_map, InsertionRequest.relabel, Function.comp_def] using
    distinct.map (f.prodMap f).injective

variable [Fintype V]

private def pullArcs (f : V ↪ W) (G : Arcs W) : Arcs V :=
  univ.filter fun e => (f.prodMap f) e ∈ G

omit [DecidableEq V] in
private theorem map_pullArcs (f : V ↪ W) {G : Arcs W} {H : Arcs V}
    (sub : G ⊆ H.map (f.prodMap f)) : (pullArcs f G).map (f.prodMap f) = G := by
  ext e
  constructor
  · intro h
    obtain ⟨a, member, rfl⟩ := mem_map.mp h
    exact (mem_filter.mp member).2
  · intro h
    obtain ⟨a, _, eq⟩ := mem_map.mp (sub h)
    exact mem_map.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, eq ▸ h⟩, eq⟩

omit [DecidableEq V] in
private theorem pullArcs_card_le (f : V ↪ W) (G : Arcs W) : (pullArcs f G).card ≤ G.card := by
  rw [← card_map (f.prodMap f)]
  apply card_le_card
  intro e he
  obtain ⟨a, member, rfl⟩ := mem_map.mp he
  exact (mem_filter.mp member).2

private theorem pullBuilder (f : V ↪ W) {requests : List (InsertionRequest V)}
    {B : ℕ → Arcs W} (valid : InsertionBuilder (requests.map (InsertionRequest.relabel f)) B) :
    InsertionBuilder requests (fun i => pullArcs f (B i)) := by
  constructor
  · simp [pullArcs, valid.empty]
  · intro i j h e he
    exact mem_filter.mpr ⟨mem_univ _, valid.monotone h (mem_filter.mp he).2⟩
  · intro i e he
    let j : Fin (requests.map (InsertionRequest.relabel f)).length := ⟨i.val, by simp⟩
    have sub := valid.available j
    rw [insertedArcs_relabel] at sub
    exact (mem_map' _).mp (sub (mem_filter.mp he).2)
  · intro i
    let j : Fin (requests.map (InsertionRequest.relabel f)).length := ⟨i.val, by simp⟩
    have sub := valid.available j
    rw [insertedArcs_relabel] at sub
    apply (reach_relabel f).mp
    rw [map_pullArcs f sub]
    have served := valid.served j
    rw [relabel_get] at served
    exact served

end Relabel

section Padding

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem insertedArcs_append_left (initial extra : List (InsertionRequest V))
    {i : ℕ} (before : i ≤ initial.length) :
    insertedArcs (initial ++ extra) i = insertedArcs initial i := by
  simp [insertedArcs, List.take_append_of_le_length before]

omit [Fintype V] in
private theorem insertionBuilder_append_left {initial extra : List (InsertionRequest V)}
    {B : ℕ → Arcs V} (valid : InsertionBuilder (initial ++ extra) B) : InsertionBuilder initial B := by
  refine ⟨valid.empty, valid.monotone, ?_, ?_⟩
  · intro i
    let j : Fin (initial ++ extra).length := ⟨i.val, by simp; omega⟩
    simpa only [j, insertedArcs_append_left initial extra (Nat.succ_le_of_lt i.isLt)] using
      valid.available j
  · intro i
    let j : Fin (initial ++ extra).length := ⟨i.val, by simp; omega⟩
    simpa only [j, List.get_eq_getElem, List.getElem_append_left i.isLt] using valid.served j

private theorem padRequests (requests : List (InsertionRequest V)) (p : ℕ)
    (before : requests.length ≤ p) (available : p ≤ Fintype.card V ^ 2)
    (feasible : InsertionFeasible requests) (distinct : (requests.map InsertionRequest.pair).Nodup) :
    ∃ extra, (requests ++ extra).length = p ∧ InsertionFeasible (requests ++ extra) ∧
      ((requests ++ extra).map InsertionRequest.pair).Nodup := by
  let used := (requests.map InsertionRequest.pair).toFinset
  have usedSize : used.card = requests.length := by
    simp [used, List.toFinset_card_of_nodup distinct]
  let unused := (univ : Finset (V × V)) \ used
  have unusedSize : unused.card = Fintype.card V ^ 2 - requests.length := by
    simp [unused, card_sdiff_of_subset (subset_univ _), usedSize, pow_two]
  obtain ⟨more, moreSub, moreSize⟩ :=
    exists_subset_card_eq (s := unused) (show p - requests.length ≤ unused.card by omega)
  let extra := more.toList.map fun d => InsertionRequest.mk univ d
  refine ⟨extra, ?_, ?_, ?_⟩
  · simp [extra, moreSize, Nat.add_sub_of_le before]
  · intro i
    by_cases first : i.val < requests.length
    · rw [insertedArcs_append_left requests extra (Nat.succ_le_of_lt first)]
      simpa only [List.get_eq_getElem, List.getElem_append_left first] using feasible ⟨i.val, first⟩
    · have full : ((requests ++ extra).get i).added = univ := by
        simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt first), extra]
      apply reach_mono (insertedArcs_contains (requests ++ extra) i)
      apply Relation.ReflTransGen.single
      change ((requests ++ extra).get i).pair ∈ ((requests ++ extra).get i).added
      rw [full]
      exact mem_univ _
  · have pairs : extra.map InsertionRequest.pair = more.toList := by
      simp [extra, List.map_map, Function.comp_def]
    rw [List.map_append, pairs]
    apply List.nodup_append'.mpr
    refine ⟨distinct, Finset.nodup_toList _, ?_⟩
    rw [← List.disjoint_toFinset_iff_disjoint, Finset.toList_toFinset]
    exact disjoint_left.mpr fun d hd hmore => (mem_sdiff.mp (moreSub hmore)).2 hd

end Padding

/-- Choose a desired number of the lattice demands and extend their trace
to exactly `p` distinct requests on `n` vertices. -/
theorem latticeLower_exact_counts {n p : ℕ} (hp : p ≤ n ^ 2) (positive : 0 < steps)
    (size : (steps + 1) * rows ≤ n) (fits : LatticeFits steps rows slopes starts) :
    ∃ requests : List (InsertionRequest (Fin n)), requests.length = p ∧
      InsertionFeasible requests ∧ (requests.map InsertionRequest.pair).Nodup ∧
      ∀ B, InsertionBuilder requests B → min p (slopes * starts) * steps ≤ (B p).card := by
  let m := min p (slopes * starts)
  have enough : m ≤ (univ : Finset (LatticeLine slopes starts)).card := by
    simp [m]
  obtain ⟨lines, _, lineCount⟩ := exists_subset_card_eq enough
  let f : LayerGrid steps rows ↪ Fin n := finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb size)
  let initial := (latticeRounds fits lines).map (InsertionRequest.relabel f)
  have baseCount : initial.length = m := by simp [initial, latticeRounds_length, lineCount]
  obtain ⟨extra, len, ok, distinct⟩ := padRequests initial p
    (baseCount.symm ▸ min_le_left p (slopes * starts)) (by simpa using hp)
    (relabel_feasible f (latticeRounds_feasible fits lines))
    (relabel_distinct f (latticeRounds_distinct fits positive lines))
  refine ⟨initial ++ extra, len, ok, distinct, ?_⟩
  intro B legal
  have original := pullBuilder f (insertionBuilder_append_left legal)
  calc
    m * steps = lines.card * steps := by rw [lineCount]
    _ ≤ (pullArcs f (B lines.card)).card := theorem3_lattice_lower fits lines original
    _ ≤ (B lines.card).card := pullArcs_card_le f _
    _ ≤ (B p).card := card_le_card (legal.monotone (lineCount ▸ min_le_left p (slopes * starts)))

private theorem dense_lattice_parameters {n p : ℕ} (hn : 64 ≤ n) (hp : 0 < p) (range : p ≤ n ^ 2) :
    ∃ steps rows slopes starts : ℕ, 0 < steps ∧ (steps + 1) * rows ≤ n ∧
      LatticeFits steps rows slopes starts ∧
      (n * p) ^ 2 ≤ (288 * (min p (slopes * starts) * steps)) ^ 3 := by
  let steps := Nat.nthRoot 3 (n ^ 2 / p)
  let rows := n / (2 * steps)
  let starts := rows / 2
  let slopes := starts / steps + 1
  have rootPos : 1 ≤ steps := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr (by
    simpa using (Nat.le_div_iff_mul_le hp).mpr (show 1 * p ≤ n ^ 2 by simpa using range))
  have rootBelow : steps ^ 3 * p ≤ n ^ 2 :=
    (Nat.mul_le_mul_right p (Nat.pow_nthRoot_le_iff.mpr (Or.inl (by decide)))).trans
      (Nat.div_mul_le_self _ _)
  have rootAbove : n ^ 2 < (steps + 1) ^ 3 * p :=
    (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) _)
  have stepSize : 4 * steps ≤ n := by
    by_contra! large
    have cube := Nat.pow_lt_pow_left large (by decide : 3 ≠ 0)
    rw [mul_pow] at cube
    have rootSlope : steps ^ 3 ≤ n ^ 2 :=
      (by simpa using Nat.mul_le_mul_left (steps ^ 3) (show 1 ≤ p by omega) :
        steps ^ 3 ≤ steps ^ 3 * p).trans rootBelow
    have limit : 4 ^ 3 * steps ^ 3 ≤ n ^ 3 := by
      calc
        _ ≤ 4 ^ 3 * n ^ 2 := Nat.mul_le_mul_left _ rootSlope
        _ ≤ n * n ^ 2 := Nat.mul_le_mul_right _ (show 4 ^ 3 ≤ n by exact hn)
        _ = _ := by ring
    exact (not_lt_of_ge limit) cube
  have twicePos : 0 < 2 * steps := by omega
  have twoRows : 2 ≤ rows := (Nat.le_div_iff_mul_le twicePos).mpr (by
    rw [← Nat.mul_assoc]
    exact stepSize)
  have rowsEnough : n ≤ 4 * steps * rows := by
    calc
      n ≤ (2 * steps) * (rows + 1) := (Nat.lt_mul_div_succ n twicePos).le
      _ ≤ (2 * steps) * (2 * rows) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have enoughStarts : rows ≤ 3 * starts := by
    have positive : 1 ≤ starts := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by simpa using twoRows)
    have split : rows % 2 + 2 * starts = rows := Nat.mod_add_div rows 2
    have remain := Nat.mod_lt rows (by decide : 0 < 2)
    omega
  have enoughSlopes : starts ≤ steps * slopes := (Nat.lt_mul_div_succ starts rootPos).le
  have fits : LatticeFits steps rows slopes starts := by
    have rise : steps * (slopes - 1) ≤ starts := by
      simpa [slopes, Nat.mul_comm] using Nat.div_mul_le_self starts steps
    have low : starts * 2 ≤ rows := Nat.div_mul_le_self rows 2
    unfold LatticeFits
    omega
  have size : (steps + 1) * rows ≤ n := by
    calc
      _ ≤ (2 * steps) * rows := Nat.mul_le_mul_right _ (by omega)
      _ = rows * (2 * steps) := Nat.mul_comm _ _
      _ ≤ n := Nat.div_mul_le_self _ _
  have approxN : n ≤ 12 * steps * starts := by
    calc
      _ ≤ 4 * steps * rows := rowsEnough
      _ ≤ 4 * steps * (3 * starts) := Nat.mul_le_mul_left _ enoughStarts
      _ = _ := by ring
  have approxP : p ≤ 144 * (slopes * starts) := by
    refine Nat.le_of_mul_le_mul_left (c := steps ^ 3) ?_ (Nat.pow_pos rootPos)
    calc
      steps ^ 3 * p ≤ n ^ 2 := rootBelow
      _ ≤ (12 * steps * starts) ^ 2 := Nat.pow_le_pow_left approxN 2
      _ = (144 * steps ^ 2 * starts) * starts := by ring
      _ ≤ (144 * steps ^ 2 * starts) * (steps * slopes) := Nat.mul_le_mul_left _ enoughSlopes
      _ = _ := by ring
  have enough : p ≤ 144 * min p (slopes * starts) := by
    rcases le_total p (slopes * starts) with h | h
    · rw [min_eq_left h]
      omega
    · rwa [min_eq_right h]
  refine ⟨steps, rows, slopes, starts, rootPos, size, fits, ?_⟩
  calc
    (n * p) ^ 2 = n ^ 2 * (p * p) := by ring
    _ ≤ ((steps + 1) ^ 3 * p) * (p * p) := Nat.mul_le_mul_right _ rootAbove.le
    _ = ((steps + 1) * p) ^ 3 := by ring
    _ ≤ (288 * (min p (slopes * starts) * steps)) ^ 3 := Nat.pow_le_pow_left (by
      calc
        _ ≤ (2 * steps) * p := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (2 * steps) * (144 * min p (slopes * starts)) := Nat.mul_le_mul_left _ enough
        _ = _ := by ring) 3

private theorem chain_lower {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (range : p ≤ n ^ 2) :
    ∃ requests : List (InsertionRequest (Fin n)), requests.length = p ∧
      InsertionFeasible requests ∧ (requests.map InsertionRequest.pair).Nodup ∧
      ∀ B, InsertionBuilder requests B → n - 1 ≤ (B p).card := by
  simpa [min_eq_right (show 1 ≤ p from hp)] using
    (latticeLower_exact_counts (steps := n - 1) (rows := 1) (slopes := 1) (starts := 1)
      range (show 0 < n - 1 by omega) (by omega) (by simp [LatticeFits]))

/-- The cited edge-insertion lower bound, with exact vertex and distinct
round counts. Cubing gives an integer statement of the two-thirds power. -/
theorem theorem3_insertion_adversary {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (range : p ≤ n ^ 2) :
    ∃ requests : List (InsertionRequest (Fin n)), requests.length = p ∧
      InsertionFeasible requests ∧ (requests.map InsertionRequest.pair).Nodup ∧
      ∀ B, InsertionBuilder requests B →
        n ≤ 288 * (B p).card ∧ (n * p) ^ 2 ≤ (288 * (B p).card) ^ 3 := by
  by_cases dense : 64 ≤ n ∧ n ≤ p ^ 2
  · obtain ⟨steps, rows, slopes, starts, positive, size, fits, power⟩ :=
      dense_lattice_parameters dense.1 hp range
    obtain ⟨requests, len, ok, distinct, force⟩ := latticeLower_exact_counts range positive size fits
    refine ⟨requests, len, ok, distinct, fun B legal => ?_⟩
    have bound := power.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left 288 (force B legal)) 3)
    refine ⟨?_, bound⟩
    by_contra! small
    have cube := Nat.pow_lt_pow_left small (by decide : 3 ≠ 0)
    have opposite : n ^ 3 ≤ (n * p) ^ 2 := by
      calc
        _ = n ^ 2 * n := by ring
        _ ≤ n ^ 2 * (p ^ 2) := Nat.mul_le_mul_left _ dense.2
        _ = _ := by ring
    exact (not_lt_of_ge (opposite.trans bound)) cube
  · obtain ⟨requests, len, ok, distinct, force⟩ := chain_lower hn hp range
    refine ⟨requests, len, ok, distinct, fun B legal => ?_⟩
    have linear : n ≤ 2 * (B p).card := by have := force B legal; omega
    refine ⟨by omega, ?_⟩
    by_cases small : p ^ 2 ≤ n
    · calc
        (n * p) ^ 2 = n ^ 2 * p ^ 2 := by ring
        _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ small
        _ = n ^ 3 := by ring
        _ ≤ (288 * (B p).card) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    · have tiny : n < 64 := by
        by_contra! h
        exact dense ⟨h, (Nat.le_of_lt (Nat.lt_of_not_ge small))⟩
      have cube : n ^ 2 ≤ 288 * (B p).card := by
        calc
          _ ≤ 64 * n := by simpa [pow_two] using Nat.mul_le_mul_right n tiny.le
          _ ≤ _ := by omega
      calc
        (n * p) ^ 2 ≤ (n * n ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ range) 2
        _ = (n ^ 2) ^ 3 := by ring
        _ ≤ (288 * (B p).card) ^ 3 := Nat.pow_le_pow_left cube 3

/-- Theorem 3's edge lower bound, with one uniform constant. -/
theorem theorem3_lower {n p : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (range : p ≤ n ^ 2) :
    ∃ requests : List (InsertionRequest (Fin n)), requests.length = p ∧
      InsertionFeasible requests ∧ (requests.map InsertionRequest.pair).Nodup ∧
      ∀ B, InsertionBuilder requests B →
        ((n : ℝ) * (p : ℝ)) ^ (2 / 3 : ℝ) + (n : ℝ) ≤ 576 * ((B p).card : ℝ) := by
  obtain ⟨requests, len, ok, distinct, h⟩ := theorem3_insertion_adversary hn hp range
  refine ⟨requests, len, ok, distinct, fun B legal => ?_⟩
  obtain ⟨linear, cube⟩ := h B legal
  let x := (n : ℝ) * (p : ℝ)
  have x0 : 0 ≤ x := by positivity
  have powEq : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul x0]
    norm_num [Real.rpow_two]
  have cubeR : x ^ 2 ≤ (288 * ((B p).card : ℝ)) ^ 3 := by
    dsimp [x]
    exact_mod_cast cube
  have bound : x ^ (2 / 3 : ℝ) ≤ 288 * ((B p).card : ℝ) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
      (powEq.symm ▸ cubeR)
  have linearR : (n : ℝ) ≤ 288 * ((B p).card : ℝ) := by exact_mod_cast linear
  linarith only [bound, linearR]

end OnlineReachabilityPreservers
