import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.List.ChainOfFn
import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.OutputAverageDistinctCleaning

/-! Short bridge projections from the incidence graph. -/

namespace OnlineReachabilityPreservers

open SimpleGraph Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Two edge-disjoint cycles through the given vertex have combined
length greater than twice the cutoff. -/
def NoShortCyclePairAt {A : Type*} (G : SimpleGraph A) (k : ℕ) (a : A) : Prop :=
  ∀ (x y : G.Walk a a), x.IsCycle → y.IsCycle → Disjoint x.edgeSet y.edgeSet →
    2*k < x.length+y.length

theorem NoShortCyclePairAt.mono {A : Type*} {G : SimpleGraph A} {j k : ℕ} {a : A}
    (free : NoShortCyclePairAt G k a) (small : j ≤ k) : NoShortCyclePairAt G j a := by
  intro x y xc yc separate
  exact (Nat.mul_le_mul_left 2 small).trans_lt (free x y xc yc separate)

/-- Any two edge-disjoint cycles based at the same vertex have combined
length greater than twice the cutoff. -/
def NoShortCyclePair {A : Type*} (G : SimpleGraph A) (k : ℕ) : Prop :=
  ∀ a, NoShortCyclePairAt G k a

theorem NoShortCyclePair.mono {A : Type*} {G : SimpleGraph A} {j k : ℕ}
    (free : NoShortCyclePair G k) (small : j ≤ k) : NoShortCyclePair G j := by
  intro a x y xc yc disjoint
  exact (Nat.mul_le_mul_left 2 small).trans_lt (free a x y xc yc disjoint)

/-- Incidence girth above the cutoff implies the cycle-pair criterion. -/
theorem NoShortCyclePair.of_egirth {A : Type*} {G : SimpleGraph A} {k : ℕ}
    (girth : (k:ℕ∞) < G.egirth) : NoShortCyclePair G k := by
  intro a x y xc yc _
  have first := ENat.natCast_lt_natCast.mp (girth.trans_le xc.egirth_le_length)
  have second := ENat.natCast_lt_natCast.mp (girth.trans_le yc.egirth_le_length)
  omega

private theorem short_circuit_injective_at_revisits {A : Type*} {G : SimpleGraph A}
    {v : A} {w : G.Walk v v} (trail : w.IsTrail) {k : ℕ}
    (free : ∀ {i j}, i < j → j < w.length → w.getVert i = w.getVert j →
      NoShortCyclePairAt G k (w.getVert i))
    (short : w.length ≤ 2*k) :
    Set.InjOn w.getVert {i | i < w.length} := by
  classical
  have cannot {i j : ℕ} (earlier : i < j) (inside : j < w.length)
      (same : w.getVert i = w.getVert j) : False := by
    have atEnd : (w.drop i).getVert (j-i) = w.getVert i := by
      rw [Walk.drop_getVert, Nat.add_sub_of_le earlier.le]
      exact same.symm
    let a := ((w.drop i).take (j-i)).copy rfl atEnd
    let b := ((w.drop j).append (w.take i)).copy same.symm rfl
    have aLength : a.length = j-i := by
      simp only [a,Walk.length_copy,Walk.take_length,Walk.drop_length]
      exact min_eq_left (Nat.sub_le_sub_right inside.le i)
    have bLength : b.length = w.length-j+i := by
      simp only [b,Walk.length_copy,Walk.length_append,Walk.drop_length,Walk.take_length]
      rw [min_eq_left (earlier.le.trans inside.le)]
    have aTrail : a.IsTrail := by
      rw [Walk.isTrail_def]
      simp only [a,Walk.edges_copy,Walk.edges_take,Walk.edges_drop]
      exact (List.take_sublist _ _).nodup ((List.drop_sublist _ _).nodup trail.edges_nodup)
    have bTrail : b.IsTrail := by
      rw [Walk.isTrail_def]
      simp only [b,Walk.edges_copy,Walk.edges_append,Walk.edges_take,Walk.edges_drop]
      refine List.nodup_append.mpr ⟨(List.drop_sublist _ _).nodup trail.edges_nodup,
        (List.take_sublist _ _).nodup trail.edges_nodup,?_⟩
      intro x hx y hy eq
      exact List.disjoint_take_drop trail.edges_nodup earlier.le hy (eq ▸ hx)
    have aNonempty : a ≠ .nil := by
      intro nil
      simp only [nil,Walk.length_nil] at aLength
      omega
    have bNonempty : b ≠ .nil := by
      intro nil
      simp only [nil,Walk.length_nil] at bLength
      omega
    have aCycle : a.IsCircuit := ⟨aTrail,aNonempty⟩
    have bCycle : b.IsCircuit := ⟨bTrail,bNonempty⟩
    have supports : Disjoint a.edgeSet b.edgeSet := by
      rw [Set.disjoint_left]
      intro e ea eb
      change e ∈ a.edges at ea
      change e ∈ b.edges at eb
      simp only [a,Walk.edges_copy,Walk.edges_take,Walk.edges_drop] at ea
      simp only [b,Walk.edges_copy,Walk.edges_append,Walk.edges_take,Walk.edges_drop,List.mem_append] at eb
      obtain tail | head := eb
      · have shift : w.edges.drop j = (w.edges.drop i).drop (j-i) := by
          rw [List.drop_drop, Nat.add_sub_of_le earlier.le]
        have nodup := (List.drop_sublist i w.edges).nodup trail.edges_nodup
        exact List.disjoint_take_drop nodup le_rfl ea (shift ▸ tail)
      · exact List.disjoint_take_drop trail.edges_nodup le_rfl head (List.mem_of_mem_take ea)
    have cycles : Disjoint a.cycleBypass.edgeSet b.cycleBypass.edgeSet := by
      apply Disjoint.mono _ _ supports
      · exact a.edges_cycleBypass_subset_edges
      · exact b.edges_cycleBypass_subset_edges
    have long := free earlier inside same _ _ aCycle.isCycle_cycleBypass bCycle.isCycle_cycleBypass cycles
    have aShort := a.length_cycleBypass_le_length
    have bShort := b.length_cycleBypass_le_length
    omega
  intro i hi j hj same
  change i < w.length at hi
  change j < w.length at hj
  rcases lt_trichotomy i j with ij | eq | ji
  · exact (cannot ij hj same).elim
  · exact eq
  · exact (cannot ji hi same.symm).elim

/-- A short trail cannot repeat a vertex before it closes. Such a repeat
would give two edge-disjoint circuits based at that vertex, and hence a
pair of shorter simple cycles there. -/
theorem NoShortCyclePair.getVert_injective {A : Type*} {G : SimpleGraph A}
    {v : A} {w : G.Walk v v} (trail : w.IsTrail) {k : ℕ}
    (free : NoShortCyclePair G k) (short : w.length ≤ 2*k) :
    Set.InjOn w.getVert {i | i < w.length} :=
  short_circuit_injective_at_revisits trail (fun {_ _} _ _ _ => free _) short

/-- The cycle-pair condition is equivalent to vertex injectivity before
closure on every closed trail of length at most twice the cutoff. -/
theorem noShortCyclePair_iff_short_trails {A : Type*} {G : SimpleGraph A} {k : ℕ} :
    NoShortCyclePair G k ↔ ∀ a (w : G.Walk a a), w.IsTrail → w.length ≤ 2*k →
      Set.InjOn w.getVert {i | i < w.length} := by
  constructor
  · intro free _ _ trail short
    exact free.getVert_injective trail short
  · intro injective a x y xc yc disjoint
    by_contra! short
    have trail : (x.append y).IsTrail :=
      (Walk.isTrail_append x y).mpr ⟨xc.isTrail,yc.isTrail,Set.disjoint_left.mp disjoint⟩
    have fit : (x.append y).length ≤ 2*k := by rwa [Walk.length_append]
    have xPos := xc.three_le_length
    have yPos := yc.three_le_length
    have zero : 0 < (x.append y).length := by rw [Walk.length_append]; omega
    have between : x.length < (x.append y).length := by rw [Walk.length_append]; omega
    have revisit : (x.append y).getVert 0 = (x.append y).getVert x.length := by
      simp [Walk.getVert_append]
    have equal := injective a (x.append y) trail fit zero between revisit
    omega

/-- An edge-injective homomorphism pulls a pointwise cycle-pair
condition back to a vertex. Projected closed trails contain cycles
through the same projected vertex. -/
theorem NoShortCyclePairAt.of_edge_injective_hom {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    {k : ℕ} (f : G →g H) {a : A} (free : NoShortCyclePairAt H k (f a))
    (injective : Set.InjOn (Sym2.map f) G.edgeSet) : NoShortCyclePairAt G k a := by
  classical
  intro x y xc yc disjoint
  have mapped (w : G.Walk a a) (cycle : w.IsCycle) : (w.map f).IsCircuit := by
    refine ⟨?_,?_⟩
    · rw [Walk.isTrail_def,Walk.edges_map]
      exact cycle.edges_nodup.map_on (fun _ left _ right eq =>
        injective (w.edges_subset_edgeSet left) (w.edges_subset_edgeSet right) eq)
    · intro nil
      have length := cycle.three_le_length
      rw [← Walk.length_map (f := f),nil,Walk.length_nil] at length
      omega
  have separate : Disjoint (x.map f).edgeSet (y.map f).edgeSet := by
    rw [Walk.edgeSet_map,Walk.edgeSet_map,Set.disjoint_left]
    rintro e ⟨left,insideX,eX⟩ ⟨right,insideY,eY⟩
    have same := injective (x.edges_subset_edgeSet insideX) (y.edges_subset_edgeSet insideY)
      (eX.trans eY.symm)
    exact Set.disjoint_left.mp disjoint insideX (same.symm ▸ insideY)
  have cycles : Disjoint (x.map f).cycleBypass.edgeSet (y.map f).cycleBypass.edgeSet :=
    separate.mono (x.map f).edges_cycleBypass_subset_edges (y.map f).edges_cycleBypass_subset_edges
  have long := free _ _ (mapped x xc).isCycle_cycleBypass (mapped y yc).isCycle_cycleBypass cycles
  have reduced := Nat.add_le_add (x.map f).length_cycleBypass_le_length (y.map f).length_cycleBypass_le_length
  rw [Walk.length_map,Walk.length_map] at reduced
  exact long.trans_le reduced

/-- An injective graph homomorphism preserves the absence of short pairs
on the smaller graph. -/
theorem NoShortCyclePair.of_injective_hom {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B} {k : ℕ}
    (free : NoShortCyclePair H k) (f : G →g H) (injective : Function.Injective f) :
    NoShortCyclePair G k := fun a =>
  (free (f a)).of_edge_injective_hom f (fun {_ _} _ _ eq => Sym2.map.injective injective eq)

/-- The bipartite graph on row labels and vertex labels, with an edge for
each incidence. The directed order inside a row plays no role here. -/
def pathIncidenceGraph {I V : Type*} (paths : I → List V) : SimpleGraph (I ⊕ V) where
  Adj
    | .inl i, .inr v => v ∈ paths i
    | .inr v, .inl i => v ∈ paths i
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

section Projection

variable {I J V W : Type*} [DecidableEq V] [DecidableEq W]

private def incidenceSlots {pieces : J → List W} {d : ℕ} (b : Bridge (Before pieces) d) :
    Fin (d+2) → J := Fin.snoc b.arc b.river

private theorem incidenceSlots_injective {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) : Function.Injective (incidenceSlots b) :=
  Fin.snoc_injective_of_injective b.distinctArcs (fun ⟨i,hi⟩ => b.river_ne_arc i hi.symm)

private theorem incidence_next_arc {d : ℕ} (a : Fin (d+1)) :
    (a.castSucc : Fin (d+2))+1 = a.succ := by
  apply Fin.ext
  simp only [Fin.val_add,Fin.val_castSucc,Fin.val_one,Fin.val_succ]
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ a.isLt)

private theorem incidence_next_river (d : ℕ) : (Fin.last (d+1):Fin (d+2))+1 = 0 := by
  apply Fin.ext
  simp

private theorem incidence_next_ne {d : ℕ} (i : Fin (d+2)) : i ≠ i+1 := by
  refine Fin.lastCases (motive := fun i : Fin (d+2) => i ≠ i+1) ?_ ?_ i
  · rw [incidence_next_river]
    intro eq
    have same := congrArg Fin.val eq
    simp at same
  · intro a
    rw [incidence_next_arc]
    intro eq
    have same := congrArg Fin.val eq
    simp at same

private theorem incidence_slot_corners {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (i : Fin (d+2)) :
    b.vertex i ∈ pieces (incidenceSlots b i) ∧ b.vertex (i+1) ∈ pieces (incidenceSlots b i) := by
  refine Fin.lastCases (motive := fun i => b.vertex i ∈ pieces (incidenceSlots b i) ∧
    b.vertex (i+1) ∈ pieces (incidenceSlots b i)) ?_ ?_ i
  · rw [incidenceSlots,Fin.snoc_last,incidence_next_river]
    exact ⟨b.riverStep.2.1,b.riverStep.1⟩
  · intro a
    rw [incidenceSlots,Fin.snoc_castSucc,incidence_next_arc]
    exact ⟨(b.arcStep a).1,(b.arcStep a).2.1⟩

private def incidenceCycleVertex {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : ℕ) : I ⊕ V :=
  let j : Fin (d+2) := ⟨(i/2)%(d+2),Nat.mod_lt _ (by omega)⟩
  if i%2 = 0 then .inr (corners j) else .inl (slots j)

omit [DecidableEq V] in
private theorem incidence_cycle_even {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : Fin (d+2)) : incidenceCycleVertex corners slots (2*i.val) = .inr (corners i) := by
  simp [incidenceCycleVertex,show 2*i.val/2 = i.val by omega,
    show (2*i.val)%2 = 0 by omega,Nat.mod_eq_of_lt i.isLt]

omit [DecidableEq V] in
private theorem incidence_cycle_odd {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : Fin (d+2)) : incidenceCycleVertex corners slots (2*i.val+1) = .inl (slots i) := by
  simp [incidenceCycleVertex,show (2*i.val+1)/2 = i.val by omega,
    show (2*i.val+1)%2 = 1 by omega,Nat.mod_eq_of_lt i.isLt]

omit [DecidableEq V] in
private theorem incidence_cycle_next {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I)
    (i : Fin (d+2)) : incidenceCycleVertex corners slots (2*i.val+2) = .inr (corners (i+1)) := by
  have index : (⟨(i.val+1)%(d+2),Nat.mod_lt _ (by omega)⟩ : Fin (d+2)) = i+1 := by
    apply Fin.ext
    simp [Fin.val_add]
  simp only [incidenceCycleVertex,show (2*i.val+2)/2 = i.val+1 by omega,
    show (2*i.val+2)%2 = 0 by omega,ite_true,index]

omit [DecidableEq V] in
private theorem incidence_cycle_closes {d : ℕ} (corners : Fin (d+2) → V) (slots : Fin (d+2) → I) :
    incidenceCycleVertex corners slots (2*(d+2)) = incidenceCycleVertex corners slots 0 := by
  simp [incidenceCycleVertex,show 2*(d+2)/2 = d+2 by omega,show (2*(d+2))%2 = 0 by omega]

omit [DecidableEq V] in
private theorem projected_bridge_incidence_injective {paths : I → List V} {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (rowSafe : ∀ {i j}, i ≠ j → parent i = parent j → pieces i ≠ [] → pieces j ≠ [] →
      NoShortCyclePairAt (pathIncidenceGraph paths) (d+2) (.inl (parent i)))
    (vertexSafe : ∀ {x y}, x ≠ y → project x = project y →
      (∃ i, x ∈ pieces i) → (∃ j, y ∈ pieces j) →
      NoShortCyclePairAt (pathIncidenceGraph paths) (d+2) (.inr (project x))) :
    Function.Injective (project ∘ b.vertex) ∧ Function.Injective (parent ∘ incidenceSlots b) := by
  let slots := parent ∘ incidenceSlots b
  let corners := project ∘ b.vertex
  let node := incidenceCycleVertex corners slots
  have even (i : Fin (d+2)) : node (2*i.val) = Sum.inr (corners i) := incidence_cycle_even corners slots i
  have odd (i : Fin (d+2)) : node (2*i.val+1) = Sum.inl (slots i) := incidence_cycle_odd corners slots i
  have next (i : Fin (d+2)) : node (2*i.val+2) = Sum.inr (corners (i+1)) := incidence_cycle_next corners slots i
  let support := List.ofFn (fun i : Fin (2*(d+2)+1) => node i.val)
  have nonempty : support ≠ [] := by simp [support]
  have chain : support.IsChain (pathIncidenceGraph paths).Adj := by
    refine List.isChain_ofFn.mpr ?_
    intro t ht
    change (pathIncidenceGraph paths).Adj (node t) (node (t+1))
    let i : Fin (d+2) := ⟨t/2,by omega⟩
    by_cases parity : t%2 = 0
    · have h : t = 2*i.val := by dsimp only [i]; omega
      rw [h,even,odd]
      exact members (incidence_slot_corners b i).1
    · have h : t = 2*i.val+1 := by dsimp only [i]; omega
      rw [h,odd,show 2*i.val+1+1 = 2*i.val+2 by omega,next]
      exact members (incidence_slot_corners b i).2
  have first : support.head nonempty = node 0 := List.head_ofFn nonempty
  have last : support.getLast nonempty = node 0 := by
    rw [List.getLast_ofFn]
    change node (2*(d+2)+1-1) = node 0
    rw [Nat.add_sub_cancel]
    exact incidence_cycle_closes corners slots
  let walk := (Walk.ofSupport support nonempty chain).copy first last
  have length : walk.length = 2*(d+2) := by
    simp only [walk,Walk.length_copy,Walk.length_ofSupport,support,List.length_ofFn]
    omega
  have atIndex {t : ℕ} (fit : t ≤ walk.length) : walk.getVert t = node t := by
    rw [walk.getVert_eq_support_getElem fit]
    simp only [walk,Walk.support_copy,Walk.support_ofSupport,support,List.getElem_ofFn]
  let edgeRow (t : Fin (2*(d+2))) : Fin (d+2) := ⟨t.val/2,by omega⟩
  let edgeCorner (t : Fin (2*(d+2))) : Fin (d+2) :=
    if t.val%2 = 0 then edgeRow t else edgeRow t+1
  have cornerEven (t : Fin (2*(d+2))) (parity : t.val%2 = 0) : edgeCorner t = edgeRow t := ite_eq_left parity
  have cornerOdd (t : Fin (2*(d+2))) (parity : t.val%2 ≠ 0) : edgeCorner t = edgeRow t+1 := ite_eq_right parity
  have cornerMem (t : Fin (2*(d+2))) : b.vertex (edgeCorner t) ∈ pieces (incidenceSlots b (edgeRow t)) := by
    by_cases parity : t.val%2 = 0
    · simpa only [cornerEven t parity] using (incidence_slot_corners b (edgeRow t)).1
    · simpa only [cornerOdd t parity] using (incidence_slot_corners b (edgeRow t)).2
  have edgeAt (t : Fin (2*(d+2))) : walk.edges[t.val]'(by rw [walk.length_edges,length]; exact t.isLt) =
      s(Sum.inl (slots (edgeRow t)),Sum.inr (corners (edgeCorner t))) := by
    rw [Walk.getElem_edges,atIndex (by omega),atIndex (by omega)]
    by_cases parity : t.val%2 = 0
    · have h : t.val = 2*(edgeRow t).val := by dsimp only [edgeRow]; omega
      rw [h,even,odd,cornerEven t parity,Sym2.eq_swap]
    · have h : t.val = 2*(edgeRow t).val+1 := by dsimp only [edgeRow]; omega
      rw [h,odd,show 2*(edgeRow t).val+1+1 = 2*(edgeRow t).val+2 by omega,next,cornerOdd t parity]
  have trail : walk.IsTrail := by
    rw [Walk.isTrail_def,List.nodup_iff_injective_get]
    intro s t same
    have sFit : s.val < 2*(d+2) := by rw [← length,← walk.length_edges]; exact s.isLt
    have tFit : t.val < 2*(d+2) := by rw [← length,← walk.length_edges]; exact t.isLt
    let s' : Fin (2*(d+2)) := ⟨s.val,sFit⟩
    let t' : Fin (2*(d+2)) := ⟨t.val,tFit⟩
    have equal : s(Sum.inl (slots (edgeRow s')),Sum.inr (corners (edgeCorner s'))) =
        s(Sum.inl (slots (edgeRow t')),Sum.inr (corners (edgeCorner t'))) := by
      rw [← edgeAt s',← edgeAt t']
      exact same
    rcases Sym2.eq_iff.mp equal with ⟨row,vertex⟩ | ⟨bad,_⟩
    · obtain ⟨row,vertex⟩ := incidences (cornerMem s') (cornerMem t')
        (Sum.inl.inj row) (Sum.inr.inj vertex)
      have rows := incidenceSlots_injective b row
      have cornersEq := b.distinctVertices vertex
      have divEq : s.val/2 = t.val/2 := congrArg Fin.val rows
      apply Fin.ext
      by_cases sEven : s'.val%2 = 0 <;> by_cases tEven : t'.val%2 = 0
      · change s.val%2 = 0 at sEven
        change t.val%2 = 0 at tEven
        omega
      · rw [cornerEven s' sEven,cornerOdd t' tEven,← rows] at cornersEq
        exact (incidence_next_ne _ cornersEq).elim
      · rw [cornerOdd s' sEven,cornerEven t' tEven,← rows] at cornersEq
        exact (incidence_next_ne _ cornersEq.symm).elim
      · change s.val%2 ≠ 0 at sEven
        change t.val%2 ≠ 0 at tEven
        omega
    · cases bad
  have revisit {s t : ℕ} (before : s < t) (fit : t < walk.length)
      (same : walk.getVert s = walk.getVert t) :
      NoShortCyclePairAt (pathIncidenceGraph paths) (d+2) (walk.getVert s) := by
    have sFit := before.trans fit
    have sShort : s < 2*(d+2) := length ▸ sFit
    have tShort : t < 2*(d+2) := length ▸ fit
    let i : Fin (d+2) := ⟨s/2,by omega⟩
    let j : Fin (d+2) := ⟨t/2,by omega⟩
    have evenS (parity : s%2 = 0) : walk.getVert s = Sum.inr (corners i) := calc
      _ = node s := atIndex sFit.le
      _ = node (2*i.val) := congrArg node (by dsimp only [i]; omega)
      _ = _ := even i
    have evenT (parity : t%2 = 0) : walk.getVert t = Sum.inr (corners j) := calc
      _ = node t := atIndex fit.le
      _ = node (2*j.val) := congrArg node (by dsimp only [j]; omega)
      _ = _ := even j
    have oddS (parity : s%2 ≠ 0) : walk.getVert s = Sum.inl (slots i) := calc
      _ = node s := atIndex sFit.le
      _ = node (2*i.val+1) := congrArg node (by dsimp only [i]; omega)
      _ = _ := odd i
    have oddT (parity : t%2 ≠ 0) : walk.getVert t = Sum.inl (slots j) := calc
      _ = node t := atIndex fit.le
      _ = node (2*j.val+1) := congrArg node (by dsimp only [j]; omega)
      _ = _ := odd j
    have indicesApart (parity : s%2 = t%2) : i ≠ j := by
      intro eq
      have shared := congrArg Fin.val eq
      change s/2 = t/2 at shared
      omega
    by_cases left : s%2 = 0 <;> by_cases right : t%2 = 0
    · rw [evenS left,evenT right] at same
      rw [evenS left]
      have apart : b.vertex i ≠ b.vertex j :=
        fun eq => indicesApart (left.trans right.symm) (b.distinctVertices eq)
      exact vertexSafe apart (Sum.inr.inj same)
        ⟨incidenceSlots b i,(incidence_slot_corners b i).1⟩
        ⟨incidenceSlots b j,(incidence_slot_corners b j).1⟩
    · rw [evenS left,oddT right] at same
      cases same
    · rw [oddS left,evenT right] at same
      cases same
    · rw [oddS left,oddT right] at same
      rw [oddS left]
      have apart : incidenceSlots b i ≠ incidenceSlots b j :=
        fun eq => indicesApart (by omega) (incidenceSlots_injective b eq)
      exact rowSafe apart (Sum.inl.inj same)
        (List.ne_nil_of_mem (incidence_slot_corners b i).1) (List.ne_nil_of_mem (incidence_slot_corners b j).1)
  have injective := short_circuit_injective_at_revisits trail (fun {_ _} => revisit) length.le
  constructor
  · intro i j same
    have iFit : 2*i.val < walk.length := by rw [length]; omega
    have jFit : 2*j.val < walk.length := by rw [length]; omega
    have equal := injective iFit jFit (by rw [atIndex iFit.le,atIndex jFit.le,even,even]; exact congrArg Sum.inr same)
    apply Fin.ext
    omega
  · intro i j same
    have iFit : 2*i.val+1 < walk.length := by rw [length]; omega
    have jFit : 2*j.val+1 < walk.length := by rw [length]; omega
    have equal := injective iFit jFit (by rw [atIndex iFit.le,atIndex jFit.le,odd,odd]; exact congrArg Sum.inl same)
    apply Fin.ext
    omega

/-- The cycle-pair test is needed only where two distinct occupied
labels of the expanded family project to the same original label. -/
def Bridge.project_of_local_cycle_pairs {paths : I → List V} {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y))
    (rowSafe : ∀ {i j}, i ≠ j → parent i = parent j → pieces i ≠ [] → pieces j ≠ [] →
      NoShortCyclePairAt (pathIncidenceGraph paths) (d+2) (.inl (parent i)))
    (vertexSafe : ∀ {x y}, x ≠ y → project x = project y →
      (∃ i, x ∈ pieces i) → (∃ j, y ∈ pieces j) →
      NoShortCyclePairAt (pathIncidenceGraph paths) (d+2) (.inr (project x))) :
    Bridge (Before paths) d := by
  have projected := projected_bridge_incidence_injective b parent project
    (fun {_ _} => members) (fun {_ _ _ _} => incidences)
    (fun {_ _} => rowSafe) (fun {_ _} => vertexSafe)
  refine ⟨project ∘ b.vertex,parent ∘ b.arc,parent b.river,projected.1,?_,?_,steps b.riverStep,
    fun i => steps (b.arcStep i)⟩
  · intro i j same
    have eq : (i.castSucc : Fin (d+2)) = j.castSucc := projected.2 (by
      simpa only [Function.comp_apply,incidenceSlots,Fin.snoc_castSucc] using same)
    exact Fin.castSucc_injective _ eq
  · intro i same
    have eq : (Fin.last (d+1):Fin (d+2)) = i.castSucc := projected.2 (by
      simpa only [Function.comp_apply,incidenceSlots,Fin.snoc_last,Fin.snoc_castSucc] using same)
    have positions := congrArg Fin.val eq
    simp only [Fin.val_last,Fin.val_castSucc] at positions
    have small := i.isLt
    omega

/-- Two edge-disjoint cycles through a repeated projected label would
fit within the doubled bridge size. If none fit, transport the bridge. -/
def Bridge.project_of_no_short_cycle_pair {paths : I → List V} {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y))
    (free : NoShortCyclePair (pathIncidenceGraph paths) (d+2)) :
    Bridge (Before paths) d :=
  b.project_of_local_cycle_pairs parent project (fun {_ _} => members)
    (fun {_ _ _ _} => incidences) (fun {_ _ _} => steps) (fun _ _ _ _ => free _) (fun _ _ _ _ => free _)

/-- When the original incidence girth exceeds the size of the bridge,
a projection injective on incidences keeps its distinct labels. -/
def Bridge.project_of_incidence_girth {paths : I → List V} {pieces : J → List W} {d : ℕ}
    (b : Bridge (Before pieces) d) (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y))
    (girth : ((d+2:ℕ):ℕ∞) < (pathIncidenceGraph paths).egirth) :
    Bridge (Before paths) d :=
  b.project_of_no_short_cycle_pair parent project (fun {_ _} => members)
    (fun {_ _ _ _} => incidences) (fun {_ _ _} => steps) (.of_egirth girth)

/-- Test only the original labels with distinct occupied copies.
Comparisons and the parent order then transport the bridge cutoff. -/
theorem localOrderAdmissible_of_local_cycle_pairs_projection [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List W} {k : ℕ} {half : Bool}
    (allowed : localOrderAdmissible half k paths)
    (parent : J → I) (project : W → V) (ordered : Monotone parent)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y))
    (rowSafe : ∀ {i j}, i ≠ j → parent i = parent j → pieces i ≠ [] → pieces j ≠ [] →
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl (parent i)))
    (vertexSafe : ∀ {x y}, x ≠ y → project x = project y →
      (∃ i, x ∈ pieces i) → (∃ j, y ∈ pieces j) →
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inr (project x))) :
    localOrderAdmissible half k pieces := by
  let lift {d : ℕ} (size : d+2 ≤ k) (b : Bridge (Before pieces) d) : Bridge (Before paths) d :=
    b.project_of_local_cycle_pairs parent project (fun {_ _} => members) (fun {_ _ _ _} => incidences)
      (fun {_ _ _} => steps) (fun {_ _} diff eq first second => (rowSafe diff eq first second).mono size)
      (fun {_ _} diff eq first second => (vertexSafe diff eq first second).mono size)
  cases half
  · intro d fit
    exact ⟨fun b => (allowed fit).false (lift fit b)⟩
  · intro d fit b earlier
    let original := lift fit b
    have strict : original.arc (Fin.last d) < original.river :=
      lt_of_le_of_ne (ordered earlier.le) (original.river_ne_arc _).symm
    exact allowed fit original strict

/-- Preserve the selected cutoff under comparison-preserving projection
with distinct incidence images and no short pair of cycles. -/
theorem localOrderAdmissible_of_no_short_cycle_pair_projection [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List W} {k : ℕ} {half : Bool}
    (allowed : localOrderAdmissible half k paths) (free : NoShortCyclePair (pathIncidenceGraph paths) k)
    (parent : J → I) (project : W → V) (ordered : Monotone parent)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y)) :
    localOrderAdmissible half k pieces :=
  localOrderAdmissible_of_local_cycle_pairs_projection allowed parent project ordered
    (fun {_ _} => members) (fun {_ _ _ _} => incidences) (fun {_ _ _} => steps)
    (fun _ _ _ _ => free _) (fun _ _ _ _ => free _)

/-- Every projection that preserves comparisons and identifies no distinct
incidences preserves the bridge cutoff below the incidence girth. In half
mode the parent map respects arrival order. -/
theorem localOrderAdmissible_of_incidence_girth_projection [LinearOrder I] [LinearOrder J]
    {paths : I → List V} {pieces : J → List W} {k : ℕ} {half : Bool}
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (parent : J → I) (project : W → V) (ordered : Monotone parent)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (incidences : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) (project x) (project y)) :
    localOrderAdmissible half k pieces :=
  localOrderAdmissible_of_no_short_cycle_pair_projection allowed (.of_egirth girth) parent project
    ordered (fun {_ _} => members) (fun {_ _ _ _} => incidences) (fun {_ _ _} => steps)

end Projection

private theorem same_incidence_block {A : Type*} {n : A → ℕ} {x y : Σ a, Fin (n a)}
    (parent : x.fst = y.fst) (same : x.snd.val = y.snd.val) : x = y := by
  rcases x with ⟨a,i⟩
  rcases y with ⟨b,j⟩
  change a = b at parent
  subst b
  obtain rfl := Fin.ext same
  rfl

private theorem occupied_row_index_zero {I V : Type*} [LinearOrder I] [Fintype I] [LinearOrder V]
    {paths : I → List V} {L : ℕ} {i : ListBlockIndex paths L}
    (short : (paths i.fst).length ≤ L) (occupied : splitListPaths paths L i ≠ []) : i.snd.val = 0 := by
  obtain ⟨x,on⟩ := List.exists_mem_of_ne_nil (splitListPaths paths L i) occupied
  obtain ⟨before,position⟩ := mem_localPathBlock.mp on
  rw [← position]
  exact Nat.div_eq_of_lt ((List.idxOf_lt_length_of_mem before).trans_le short)

private theorem occupied_copy_index_zero {I V : Type*} [LinearOrder I] [Fintype I] [LinearOrder V]
    {paths : I → List V} {D : ℕ} {x : ListVertexBlockIndex paths D} {i : I}
    (short : (occurrences (fun j => (paths j).toFinset) x.fst).card ≤ D)
    (on : x ∈ splitListVertices paths D i) : x.snd.val = 0 := by
  change x ∈ (paths i).attach.map _ at on
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp on
  let supported := occurrences (fun j => (paths j).toFinset) u.val
  have present : i ∈ supported := mem_occurrences.mpr (List.mem_toFinset.mpr u.property)
  have rank : (predecessors supported i).card < supported.card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,?_⟩
    intro equal
    have earlier : i ∈ predecessors supported i := by rw [equal]; exact present
    exact (lt_irrefl i) (mem_filter.mp earlier).2
  change (predecessors supported i).card/D = 0
  exact Nat.div_eq_of_lt (rank.trans_le short)

/-- For the standard splits, only original rows longer than the path width
and vertices above the degree width need the cycle-pair test. -/
theorem listRegularizedPaths_admissible_of_local_cycle_pairs {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {paths : I → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (D L : ℕ)
    (overlong : ∀ i, L < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i))
    (overdegree : ∀ x, D < (occurrences (fun i => (paths i).toFinset) x).card →
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inr x)) :
    localOrderAdmissible half k (listRegularizedPaths paths D L) := by
  let copies := splitListVertices paths D
  let pieces := splitListPaths copies L
  let parent : ListBlockIndex copies L → I := Sigma.fst
  let project : ListVertexBlockIndex paths D → V := Sigma.fst
  have sub (i : ListBlockIndex copies L) : (pieces i).Sublist (copies (parent i)) :=
    List.filter_sublist
  have copiedSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have members {i x} (on : x ∈ pieces i) : project x ∈ paths (parent i) := by
    rw [← splitListVertices_project paths D (parent i)]
    exact List.mem_map_of_mem ((sub i).subset on)
  have incidences {i j x y} (xi : x ∈ pieces i) (yj : y ∈ pieces j)
      (row : parent i = parent j) (vertex : project x = project y) : i = j ∧ x = y := by
    have yi : y ∈ copies (parent i) := row.symm ▸ (sub j).subset yj
    have distinct : ((copies (parent i)).map project).Nodup :=
      (splitListVertices_project paths D (parent i)).symm ▸ simple (parent i)
    have same := List.inj_on_of_nodup_map distinct ((sub i).subset xi) yi vertex
    refine ⟨?_,same⟩
    by_contra apart
    exact splitListPaths_disjoint apart row xi (same.symm ▸ yj)
  have steps {i x y} (step : Before pieces i x y) : Before paths (parent i) (project x) (project y) := by
    have lifted : Before (fun j : ListBlockIndex copies L => copies (parent j)) i x y :=
      listBefore_of_sublist (copiedSimple (parent i)) (sub i) step
    exact splitListVertices_step (simple (parent i)) lifted
  have rowZero {i : ListBlockIndex copies L} (short : (paths (parent i)).length ≤ L)
      (occupied : pieces i ≠ []) : i.snd.val = 0 :=
    occupied_row_index_zero ((splitListVertices_length paths D (parent i)).trans_le short) occupied
  have rowTest {i j : ListBlockIndex copies L} (different : i ≠ j) (equal : parent i = parent j)
      (occupiedI : pieces i ≠ []) (occupiedJ : pieces j ≠ []) :
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl (parent i)) := by
    apply overlong
    by_contra! short
    have second : (paths (parent j)).length ≤ L := equal ▸ short
    exact different (same_incidence_block equal ((rowZero short occupiedI).trans
      (rowZero second occupiedJ).symm))
  have vertexZero {x : ListVertexBlockIndex paths D} {i : ListBlockIndex copies L}
      (short : (occurrences (fun i => (paths i).toFinset) (project x)).card ≤ D)
      (on : x ∈ pieces i) : x.snd.val = 0 :=
    occupied_copy_index_zero short ((sub i).subset on)
  have vertexTest {x y : ListVertexBlockIndex paths D} (different : x ≠ y) (equal : project x = project y)
      (occupiedX : ∃ i, x ∈ pieces i) (occupiedY : ∃ j, y ∈ pieces j) :
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inr (project x)) := by
    apply overdegree
    by_contra! short
    obtain ⟨i,inside⟩ := occupiedX
    obtain ⟨j,other⟩ := occupiedY
    have second : (occurrences (fun i => (paths i).toFinset) (project y)).card ≤ D := equal ▸ short
    exact different (same_incidence_block equal ((vertexZero short inside).trans
      (vertexZero second other).symm))
  exact localOrderAdmissible_of_local_cycle_pairs_projection allowed parent project
    (block_parent_mono (fun i => (copies i).toFinset) L) (fun {_ _} => members)
    (fun {_ _ _ _} => incidences) (fun {_ _ _} => steps) (fun {_ _} => rowTest) (fun {_ _} => vertexTest)

/-- When no two edge-disjoint cycles through one label fit within twice
the cutoff, both standard width splits preserve the chosen exclusion. -/
theorem listRegularizedPaths_admissible_of_no_short_cycle_pair {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {paths : I → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (free : NoShortCyclePair (pathIncidenceGraph paths) k) (D L : ℕ) :
    localOrderAdmissible half k (listRegularizedPaths paths D L) :=
  listRegularizedPaths_admissible_of_local_cycle_pairs simple allowed D L (fun _ _ => free _) (fun _ _ => free _)

/-- Both ordinary width splits project injectively on the incidences. Thus
they preserve either bridge cutoff strictly below the incidence girth. -/
theorem listRegularizedPaths_admissible_of_incidence_girth {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {paths : I → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth) (D L : ℕ) :
    localOrderAdmissible half k (listRegularizedPaths paths D L) :=
  listRegularizedPaths_admissible_of_no_short_cycle_pair simple allowed (.of_egirth girth) D L

/-- Project each incidence to the edge between its original labels. -/
def pathIncidenceGraph_hom {I J V W : Type*}
    {paths : I → List V} {pieces : J → List W} (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i)) :
    pathIncidenceGraph pieces →g pathIncidenceGraph paths :=
  ⟨Sum.map parent project,by
    intro a b h
    cases a <;> cases b
    · exact h.elim
    · exact members h
    · exact members h
    · exact h.elim⟩

/-- Restricting row labels and vertex labels does not decrease incidence
girth when each retained incidence is present in the input. -/
theorem pathIncidenceGraph_egirth_le_of_embedding {I J V W : Type*}
    {paths : I → List V} {pieces : J → List W} (parent : J → I) (project : W → V)
    (rowInjective : Function.Injective parent) (vertexInjective : Function.Injective project)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i)) :
    (pathIncidenceGraph paths).egirth ≤ (pathIncidenceGraph pieces).egirth := by
  let f := pathIncidenceGraph_hom parent project (fun {_ _} => members)
  have injective : Function.Injective f := Sum.map_injective.mpr ⟨rowInjective,vertexInjective⟩
  refine SimpleGraph.le_egirth.mpr (fun a w cycle => ?_)
  simpa only [Walk.length_map] using (cycle.map injective).egirth_le_length

/-- Test for short pairs only on rows and vertices above their original
widths. Frozen cleaning then keeps both budgets, all four caps, and M/16. -/
theorem regularization_list_frozen_of_local_cycle_pairs {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (overlong : let M := ∑ i, (paths i).length
      ∀ i, 4*M/p < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i))
    (overdegree : let M := ∑ i, (paths i).length
      ∀ x, 4*M/n < (occurrences (fun i => (paths i).toFinset) x).card →
        NoShortCyclePairAt (pathIncidenceGraph paths) k (.inr x))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  exact regularization_list_frozen_after_width_blocks_of_mass paths simple
    (listRegularizedPaths_admissible_of_local_cycle_pairs simple allowed (4*M/n) (4*M/p)
      overlong overdegree)
    hn hp dense long le_rfl (by ring_nf; omega)

/-- At any cutoff satisfying the incidence cycle-pair condition, retain
both budgets, all four starting-average caps, and at least M/16. -/
theorem regularization_list_frozen_of_no_short_cycle_pair {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (free : NoShortCyclePair (pathIncidenceGraph paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows :=
  regularization_list_frozen_of_local_cycle_pairs paths simple allowed
    (fun _ _ => free _) (fun _ _ => free _) hn hp dense long

/-- At a cutoff smaller than the incidence girth, both original budgets,
all four starting-average caps, and at least one sixteenth of the input
mass survive regularization in either bridge mode. -/
theorem regularization_list_frozen_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows :=
  regularization_list_frozen_of_no_short_cycle_pair paths simple allowed (.of_egirth girth) hn hp dense long

/-- The original-width tests also suffice for the literal starting-average witness. -/
theorem regularization_literal_frozen_of_local_cycle_pairs {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (overlong : let M := ∑ i, (paths i).length
      ∀ i, 4*M/p < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i))
    (overdegree : let M := ∑ i, (paths i).length
      ∀ x, 4*M/n < (occurrences (fun i => (paths i).toFinset) x).card →
        NoShortCyclePairAt (pathIncidenceGraph paths) k (.inr x))
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,legal,keep,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed paths distinct (fun i => (valid i).1) (fun i => (valid i).2)
      allowed two hn hp dense (by decide)
      (regularization_list_frozen_of_local_cycle_pairs paths (fun i => (valid i).2) allowed overlong overdegree hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,legal,keep,upper,caps⟩

/-- The cycle-pair criterion gives the same starting-average guarantee
for distinct nonempty literal rows. -/
theorem regularization_literal_frozen_of_no_short_cycle_pair {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (free : NoShortCyclePair (pathIncidenceGraph paths) k)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows :=
  regularization_literal_frozen_of_local_cycle_pairs paths distinct valid allowed
    (fun _ _ => free _) (fun _ _ => free _) two hn hp dense

/-- The same incidence-girth criterion gives exact starting caps in the
literal convention for cutoffs at least two. -/
theorem regularization_literal_frozen_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows :=
  regularization_literal_frozen_of_no_short_cycle_pair paths distinct valid allowed (.of_egirth girth) two hn hp dense

/-- Both budgets and the four output-average caps follow from the
cycle-pair criterion at the input cutoff. -/
theorem regularization_list_output_average_of_no_short_cycle_pair {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (free : NoShortCyclePair (pathIncidenceGraph paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 392*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  refine regularization_list_output_average_of_rectangle_splits (k := k) paths simple half ?_
    hn hp dense long (by omega) le_rfl
  intro A B D L
  let rectangle := restrictListPaths paths A B
  have rectangleSimple (i : B) : (rectangle i).Nodup := restrictListPath_nodup (simple i.val) A
  have restricted : localOrderAdmissible half k rectangle := by
    cases half
    · exact restrictListPaths_fullFree simple allowed A B
    · exact restrictListPaths_halfFree simple allowed A B
  let hom : pathIncidenceGraph rectangle →g pathIncidenceGraph paths :=
    pathIncidenceGraph_hom Subtype.val Subtype.val (fun {_ _} on => mem_restrictListPath.mp on)
  have injective : Function.Injective hom :=
    Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  exact listRegularizedPaths_admissible_of_no_short_cycle_pair rectangleSimple restricted
    (free.of_injective_hom hom injective) D L

/-- Below the incidence girth, the indexed witness can instead use the
four caps relative to its own averages, keeping both original budgets. -/
theorem regularization_list_output_average_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 392*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows :=
  regularization_list_output_average_of_no_short_cycle_pair paths simple allowed (.of_egirth girth) hn hp dense long

/-- The cycle-pair criterion supplies a literal output-average witness. -/
theorem regularization_literal_output_average_of_no_short_cycle_pair {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (free : NoShortCyclePair (pathIncidenceGraph paths) k)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 7056*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,legal,keep,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed paths distinct (fun i => (valid i).1) (fun i => (valid i).2)
      allowed two hn hp dense
      (regularization_list_output_average_of_no_short_cycle_pair paths (fun i => (valid i).2) allowed free hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,legal,keep,upper,caps⟩

/-- The output-average criterion also applies to distinct nonempty rows. -/
theorem regularization_literal_output_average_of_incidence_girth {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (girth : (k:ℕ∞) < (pathIncidenceGraph paths).egirth)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 7056*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows :=
  regularization_literal_output_average_of_no_short_cycle_pair paths distinct valid allowed (.of_egirth girth)
    two hn hp dense

private theorem pathIncidenceGraph_edge_shape {I V : Type*} {paths : I → List V}
    {e : Sym2 (I ⊕ V)} (inside : e ∈ (pathIncidenceGraph paths).edgeSet) :
    ∃ i x, x ∈ paths i ∧ e = s(Sum.inl i,Sum.inr x) := by
  revert inside
  refine Sym2.inductionOn e (fun a b inside => ?_)
  have linked := (pathIncidenceGraph paths).mem_edgeSet.mp inside
  cases a <;> cases b
  · exact linked.elim
  · exact ⟨_,_,linked,rfl⟩
  · exact ⟨_,_,linked,Sym2.eq_swap⟩
  · exact linked.elim

private theorem pathIncidenceGraph_hom_edge_injective {I J V W : Type*}
    {paths : I → List V} {pieces : J → List W} (parent : J → I) (project : W → V)
    (members : ∀ {i x}, x ∈ pieces i → project x ∈ paths (parent i))
    (unique : ∀ {i j x y}, x ∈ pieces i → y ∈ pieces j → parent i = parent j →
      project x = project y → i = j ∧ x = y) :
    Set.InjOn (Sym2.map (pathIncidenceGraph_hom parent project (fun {_ _} => members)))
      (pathIncidenceGraph pieces).edgeSet := by
  intro e one f two same
  obtain ⟨i,x,xi,rfl⟩ := pathIncidenceGraph_edge_shape one
  obtain ⟨j,y,yj,rfl⟩ := pathIncidenceGraph_edge_shape two
  change s(Sum.inl (parent i),Sum.inr (project x)) =
    s(Sum.inl (parent j),Sum.inr (project y)) at same
  rcases Sym2.eq_iff.mp same with ⟨row,vertex⟩ | ⟨impossible,_⟩
  · obtain ⟨rfl,rfl⟩ := unique xi yj (Sum.inl.inj row) (Sum.inr.inj vertex)
    rfl
  · cases impossible

/-- Consecutive path splits need the cycle-pair test only on overlong
rows of their input. -/
theorem splitListPaths_admissible_of_row_cycle_pairs {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] {paths : I → List V} {k : ℕ} {half : Bool}
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths) (L : ℕ)
    (overlong : ∀ i, L < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i)) :
    localOrderAdmissible half k (splitListPaths paths L) := by
  let pieces := splitListPaths paths L
  let parent : ListBlockIndex paths L → I := Sigma.fst
  have sub (i : ListBlockIndex paths L) : (pieces i).Sublist (paths (parent i)) := List.filter_sublist
  have incidences {i j x y} (one : x ∈ pieces i) (two : y ∈ pieces j)
      (row : parent i = parent j) (vertex : x = y) : i = j ∧ x = y := by
    refine ⟨?_,vertex⟩
    by_contra different
    exact splitListPaths_disjoint different row one (vertex.symm ▸ two)
  have rowTest {i j} (different : i ≠ j) (equal : parent i = parent j)
      (first : pieces i ≠ []) (last : pieces j ≠ []) :
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl (parent i)) := by
    apply overlong
    by_contra! short
    have other : (paths (parent j)).length ≤ L := equal ▸ short
    exact different (same_incidence_block equal
      ((occupied_row_index_zero short first).trans (occupied_row_index_zero other last).symm))
  exact localOrderAdmissible_of_local_cycle_pairs_projection allowed parent id
    (block_parent_mono (fun i => (paths i).toFinset) L)
    (fun {i _} on => (sub i).subset on) (fun {_ _ _ _} => incidences)
    (fun {i _ _} step => listBefore_of_sublist
      (paths := fun j : ListBlockIndex paths L => paths (parent j)) (simple (parent i)) (sub i) step)
    (fun {_ _} => rowTest) (fun different equal _ _ => (different equal).elim)

/-- Full bridge exclusion survives degree copying. The path split
then needs the test only at overlong rows of the actual copied graph. -/
theorem listRegularizedPaths_fullFree_of_copied_row_cycle_pairs {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {paths : I → List V} {k : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (D L : ℕ)
    (overlong : let copies := splitListVertices paths D
      ∀ i, L < (copies i).length → NoShortCyclePairAt (pathIncidenceGraph copies) k (.inl i)) :
    BridgeFree (Before (listRegularizedPaths paths D L)) k :=
  splitListPaths_admissible_of_row_cycle_pairs (half := false)
    (fun i => splitListVertices_simple paths D i (simple i))
    (free.split_list_vertices_any (·.fst) (fun {i _ _} step => splitListVertices_step (simple i) step))
    L overlong

/-- A test at the overlong rows of the original incidence graph
also suffices, since the degree projection is injective on edges. -/
theorem listRegularizedPaths_fullFree_of_row_cycle_pairs {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {paths : I → List V} {k : ℕ}
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (D L : ℕ)
    (overlong : ∀ i, L < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i)) :
    BridgeFree (Before (listRegularizedPaths paths D L)) k := by
  let copies := splitListVertices paths D
  let project : ListVertexBlockIndex paths D → V := Sigma.fst
  have members {i x} (on : x ∈ copies i) : project x ∈ paths i := by
    rw [← splitListVertices_project paths D i]
    exact List.mem_map_of_mem on
  let hom : pathIncidenceGraph copies →g pathIncidenceGraph paths :=
    pathIncidenceGraph_hom id project (fun {_ _} => members)
  have injective : Set.InjOn (Sym2.map hom) (pathIncidenceGraph copies).edgeSet := by
    refine pathIncidenceGraph_hom_edge_injective id project (fun {_ _} => members) ?_
    intro i j x y one two row vertex
    change i = j at row
    subst j
    have mapped : ((copies i).map project).Nodup :=
      (splitListVertices_project paths D i).symm ▸ simple i
    exact ⟨rfl,List.inj_on_of_nodup_map mapped one two vertex⟩
  have copiedPairs (i) (long : L < (copies i).length) :
      NoShortCyclePairAt (pathIncidenceGraph copies) k (.inl i) := by
    change L < (splitListVertices paths D i).length at long
    rw [splitListVertices_length] at long
    exact (overlong i long).of_edge_injective_hom hom injective
  exact listRegularizedPaths_fullFree_of_copied_row_cycle_pairs simple free D L copiedPairs

/-- A test after degree copying gives a starting-average witness at
any finite full cutoff, with both original budgets and M/16 retention. -/
theorem regularization_list_frozen_full_of_copied_row_cycle_pairs {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k)
    (overlong : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, 4*M/p < (copies i).length → NoShortCyclePairAt (pathIncidenceGraph copies) k (.inl i))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ BridgeFree (Before rows) k ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  exact regularization_list_frozen_after_width_blocks_of_mass (half := false) paths simple
    (listRegularizedPaths_fullFree_of_copied_row_cycle_pairs simple free (4*M/n) (4*M/p) overlong)
    hn hp dense long le_rfl (by ring_nf; omega)

/-- The copied-graph test gives the same starting caps at cutoffs of at
least two for distinct nonempty input and output rows. -/
theorem regularization_literal_frozen_full_of_copied_row_cycle_pairs {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : BridgeFree (Before paths) k)
    (overlong : let M := ∑ i, (paths i).length
      let copies := splitListVertices paths (4*M/n)
      ∀ i, 4*M/p < (copies i).length → NoShortCyclePairAt (pathIncidenceGraph copies) k (.inl i))
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) k ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,legal,keep,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (half := false) paths distinct (fun i => (valid i).1)
      (fun i => (valid i).2) free two hn hp dense (by decide)
      (regularization_list_frozen_full_of_copied_row_cycle_pairs paths (fun i => (valid i).2)
        free overlong hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,legal,keep,upper,caps⟩

/-- For full exclusion, testing the overlong rows at the original width
suffices for all four original-average caps and both budgets. -/
theorem regularization_list_frozen_full_of_row_cycle_pairs {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k)
    (overlong : let M := ∑ i, (paths i).length
      ∀ i, 4*M/p < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ BridgeFree (Before rows) k ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  exact regularization_list_frozen_after_width_blocks_of_mass (half := false) paths simple
    (listRegularizedPaths_fullFree_of_row_cycle_pairs simple free (4*M/n) (4*M/p) overlong)
    hn hp dense long le_rfl (by ring_nf; omega)

/-- The overlong-row test also gives the literal full-bridge witness
with the same starting-average guarantee. -/
theorem regularization_literal_frozen_full_of_row_cycle_pairs {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : BridgeFree (Before paths) k)
    (overlong : let M := ∑ i, (paths i).length
      ∀ i, 4*M/p < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i))
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ BridgeFree (Before rows) k ∧
      M ≤ 16*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,legal,keep,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (half := false) paths distinct (fun i => (valid i).1)
      (fun i => (valid i).2) free two hn hp dense (by decide)
      (regularization_list_frozen_full_of_row_cycle_pairs paths (fun i => (valid i).2) free overlong hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,legal,keep,upper,caps⟩

/-- For output-average cleaning, check rows of length above sixteen
and, in half mode, vertices of degree above sixteen. Rectangles needing
splits have both splitting widths at least sixteen. -/
theorem regularization_list_output_average_of_large_label_cycle_pairs {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (longRows : ∀ i, 16 < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i))
    (highVertices : half = true → ∀ x, 16 < (occurrences (fun i => (paths i).toFinset) x).card →
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inr x))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 392*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  refine regularization_list_output_average_of_dense_rectangle_splits (k := k) paths simple half ?_
    hn hp dense long (by omega) le_rfl
  intro A B
  dsimp only
  intro retained high
  let rectangle := restrictListPaths paths A B
  let m := ∑ i : B, (rectangle i).length
  let D := 2*m/n
  let L := 2*m/p
  have width {b : ℕ} (positive : 0 < b) (fit : b ≤ max n p) : 16 ≤ 2*m/b :=
    (Nat.le_div_iff_mul_le positive).mpr (by change (∑ i, (paths i).length) ≤ 49*m at retained; omega)
  have vWidth : 16 ≤ D := width hn (le_max_left _ _)
  have rWidth : 16 ≤ L := width hp (le_max_right _ _)
  have rectangleSimple (i : B) : (rectangle i).Nodup := restrictListPath_nodup (simple i.val) A
  have restricted : localOrderAdmissible half k rectangle := by
    cases half
    · exact restrictListPaths_fullFree simple allowed A B
    · exact restrictListPaths_halfFree simple allowed A B
  let hom : pathIncidenceGraph rectangle →g pathIncidenceGraph paths :=
    pathIncidenceGraph_hom Subtype.val Subtype.val (fun {_ _} on => mem_restrictListPath.mp on)
  have vertexMap : Function.Injective hom :=
    Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  have edgeMap : Set.InjOn (Sym2.map hom) (pathIncidenceGraph rectangle).edgeSet :=
    fun {_ _} _ _ same => Sym2.map.injective vertexMap same
  have rowLength (i : B) : (rectangle i).length ≤ (paths i.val).length := calc
    _ = ((paths i.val).toFinset ∩ A).card := restrictListPath_length (simple i.val) A
    _ ≤ _ := (card_le_card inter_subset_left).trans (List.toFinset_card_le _)
  have vertexDegree (x : A) : (occurrences (fun i : B => (rectangle i).toFinset) x).card ≤
      (occurrences (fun i => (paths i).toFinset) x.val).card := by
    apply card_le_card_of_injOn Subtype.val
    · intro i on
      have kept : x ∈ rectangle i := List.mem_toFinset.mp
        ((mem_occurrences (marks := fun j : B => (rectangle j).toFinset)).mp on)
      exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_restrictListPath.mp kept))
    · exact Subtype.val_injective.injOn
  have rows (i : B) (wide : L < (rectangle i).length) :
      NoShortCyclePairAt (pathIncidenceGraph rectangle) k (.inl i) := by
    have original := longRows i.val ((rWidth.trans_lt wide).trans_le (rowLength i))
    exact original.of_edge_injective_hom hom edgeMap
  cases half
  · exact listRegularizedPaths_fullFree_of_row_cycle_pairs rectangleSimple restricted D L rows
  · have vertices (x : A) (wide : D < (occurrences (fun i : B => (rectangle i).toFinset) x).card) :
        NoShortCyclePairAt (pathIncidenceGraph rectangle) k (.inr x) := by
      have original := highVertices rfl x.val ((vWidth.trans_lt wide).trans_le (vertexDegree x))
      exact original.of_edge_injective_hom hom edgeMap
    exact listRegularizedPaths_admissible_of_local_cycle_pairs rectangleSimple restricted D L rows vertices

/-- The same original-label tests certify a literal output-average
witness at cutoffs of at least two. -/
theorem regularization_literal_output_average_of_large_label_cycle_pairs {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (longRows : ∀ i, 16 < (paths i).length → NoShortCyclePairAt (pathIncidenceGraph paths) k (.inl i))
    (highVertices : half = true → ∀ x, 16 < (occurrences (fun i => (paths i).toFinset) x).card →
      NoShortCyclePairAt (pathIncidenceGraph paths) k (.inr x))
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ localOrderAdmissible half k rows ∧
      M ≤ 7056*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ listOutputAverageCaps rows := by
  obtain ⟨v,vFit,q,qFit,rows,oneToOne,nonempty,simple,legal,keep,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed paths distinct (fun i => (valid i).1)
      (fun i => (valid i).2) allowed two hn hp dense
      (regularization_list_output_average_of_large_label_cycle_pairs paths (fun i => (valid i).2)
        allowed longRows highVertices hn hp dense)
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,simple i⟩,legal,keep,upper,caps⟩

end OnlineReachabilityPreservers
