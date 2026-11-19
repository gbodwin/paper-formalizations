import OnlineReachabilityPreservers.CyclicIntersections
import OnlineReachabilityPreservers.DagReduction

/-! Close each path using private vertices. The resulting directed cycles
preserve full bridge exclusion and put each endpoint demand within one SCC. -/

namespace OnlineReachabilityPreservers.SourceAudit

inductive ReturnVertex (V I : Type*)
  | original (v : V)
  | start (i : I)
  | finish (i : I)
  | turn (i : I)
  deriving DecidableEq, Fintype

inductive ReturnPath (I : Type*)
  | main (i : I)
  | first (i : I)
  | second (i : I)
  deriving DecidableEq, Fintype

private inductive ReturnBefore {V I : Type*}
    (before : I → V → V → Prop) (inside : I → V → Prop) :
    ReturnPath I → ReturnVertex V I → ReturnVertex V I → Prop where
  | original {i u v} : before i u v → ReturnBefore before inside (.main i) (.original u) (.original v)
  | fromStart {i v} : inside i v → ReturnBefore before inside (.main i) (.start i) (.original v)
  | toFinish {i v} : inside i v → ReturnBefore before inside (.main i) (.original v) (.finish i)
  | through (i) : ReturnBefore before inside (.main i) (.start i) (.finish i)
  | first (i) : ReturnBefore before inside (.first i) (.finish i) (.turn i)
  | second (i) : ReturnBefore before inside (.second i) (.turn i) (.start i)

namespace ReturnBefore

variable {V I : Type*} {before : I → V → V → Prop} {inside : I → V → Prop}

private theorem first_endpoints {i u v} (step : ReturnBefore before inside (.first i) u v) :
    u = .finish i ∧ v = .turn i := by cases step; exact ⟨rfl,rfl⟩

private theorem second_endpoints {i u v} (step : ReturnBefore before inside (.second i) u v) :
    u = .turn i ∧ v = .start i := by cases step; exact ⟨rfl,rfl⟩

private theorem to_finish {p u i} (step : ReturnBefore before inside p u (.finish i)) :
    p = .main i := by cases step <;> rfl

private theorem from_finish {p v i} (step : ReturnBefore before inside p (.finish i) v) :
    p = .first i := by
  cases step
  rfl

private theorem to_start {p u i} (step : ReturnBefore before inside p u (.start i)) :
    p = .second i := by
  cases step
  rfl

private theorem from_start {p v i} (step : ReturnBefore before inside p (.start i) v) :
    p = .main i := by cases step <;> rfl

private theorem to_turn {p u i} (step : ReturnBefore before inside p u (.turn i)) :
    p = .first i := by
  cases step
  rfl

private theorem from_turn {p v i} (step : ReturnBefore before inside p (.turn i) v) :
    p = .second i := by
  cases step
  rfl

private theorem main_source {i u v} (step : ReturnBefore before inside (.main i) u v) :
    (∃ x, u = .original x) ∨ u = .start i := by cases step <;> simp

private theorem main_target {i u v} (step : ReturnBefore before inside (.main i) u v) :
    (∃ x, v = .original x) ∨ v = .finish i := by cases step <;> simp

private theorem compared {i u v} (step : ReturnBefore before inside (.main i) (.original u) (.original v)) :
    before i u v := by cases step; assumption

private theorem bridge_river_main {k : ℕ} (b : Bridge (ReturnBefore before inside) k) :
    ∃ i, b.river = .main i := by
  cases lab : b.river with
  | main i => exact ⟨i,rfl⟩
  | first i =>
    have river := b.riverStep
    rw [lab] at river
    have start := (first_endpoints river).1
    have edge := b.arcStep 0
    change ReturnBefore before inside (b.arc 0) (b.vertex 0) _ at edge
    rw [start] at edge
    exact (b.river_ne_arc 0 (lab.trans (from_finish edge).symm)).elim
  | second i =>
    have river := b.riverStep
    rw [lab] at river
    have start := (second_endpoints river).1
    have edge := b.arcStep 0
    change ReturnBefore before inside (b.arc 0) (b.vertex 0) _ at edge
    rw [start] at edge
    exact (b.river_ne_arc 0 (lab.trans (from_turn edge).symm)).elim

private theorem bridge_no_first {k : ℕ} (b : Bridge (ReturnBefore before inside) k)
    {r : I} (riverMain : b.river = .main r) (t : Fin (k+1)) (i : I) : b.arc t ≠ .first i := by
  intro lab
  have first := b.arcStep t
  rw [lab] at first
  obtain ⟨finish,turn⟩ := first_endpoints first
  have river := b.riverStep
  rw [riverMain] at river
  have positive : 0 < t.val := by
    by_contra! h
    have atZero : t.castSucc = 0 := Fin.ext (by change t.val = 0; omega)
    rw [atZero] at finish
    rcases main_source river with ⟨x, hx⟩ | hx <;> simp_all
  let previous : Fin (k+1) := ⟨t.val-1, by omega⟩
  have prevEnd : previous.succ = t.castSucc := Fin.ext (by change (t.val-1)+1 = t.val; omega)
  have prevStep := b.arcStep previous
  rw [prevEnd,finish] at prevStep
  have prevLabel := to_finish prevStep
  have nextExists : t.val < k := by
    by_contra! h
    have atLast : t.succ = Fin.last (k+1) := Fin.ext (by change t.val+1 = k+1; omega)
    rw [atLast] at turn
    rcases main_target river with ⟨x,hx⟩ | hx <;> simp_all
  let next : Fin (k+1) := ⟨t.val+1, by omega⟩
  have nextStart : next.castSucc = t.succ := Fin.ext rfl
  have nextStep := b.arcStep next
  rw [nextStart,turn] at nextStep
  have nextLabel := from_turn nextStep
  rw [nextLabel] at nextStep
  have start := (second_endpoints nextStep).2
  have finalExists : next.val < k := by
    by_contra! h
    have atLast : next.succ = Fin.last (k+1) := Fin.ext (by change next.val+1 = k+1; omega)
    rw [atLast] at start
    rcases main_target river with ⟨x,hx⟩ | hx <;> simp_all
  let final : Fin (k+1) := ⟨next.val+1, by omega⟩
  have finalStart : final.castSucc = next.succ := Fin.ext rfl
  have finalStep := b.arcStep final
  rw [finalStart,start] at finalStep
  have finalLabel := from_start finalStep
  have repeated := b.distinctArcs (prevLabel.trans finalLabel.symm)
  have impossible := congrArg Fin.val repeated
  change t.val-1 = t.val+1+1 at impossible
  omega

private theorem bridge_arcs_main {k : ℕ} (b : Bridge (ReturnBefore before inside) k)
    {r : I} (riverMain : b.river = .main r) (t : Fin (k+1)) : ∃ i, b.arc t = .main i := by
  cases lab : b.arc t with
  | main i => exact ⟨i,rfl⟩
  | first i => exact (bridge_no_first b riverMain t i lab).elim
  | second i =>
    have edge := b.arcStep t
    rw [lab] at edge
    have turn := (second_endpoints edge).1
    have river := b.riverStep
    rw [riverMain] at river
    have positive : 0 < t.val := by
      by_contra! h
      have atZero : t.castSucc = 0 := Fin.ext (by change t.val = 0; omega)
      rw [atZero] at turn
      rcases main_source river with ⟨x,hx⟩ | hx <;> simp_all
    let prev : Fin (k+1) := ⟨t.val-1,by omega⟩
    have prevEnd : prev.succ = t.castSucc := Fin.ext (by change (t.val-1)+1 = t.val; omega)
    have prevStep := b.arcStep prev
    rw [prevEnd,turn] at prevStep
    exact (bridge_no_first b riverMain prev i (to_turn prevStep)).elim

private theorem bridge_vertices_original {k : ℕ} (b : Bridge (ReturnBefore before inside) k)
    {r : I} (riverMain : b.river = .main r) (j : Fin (k+2)) : ∃ x, b.vertex j = .original x := by
  have river := b.riverStep
  rw [riverMain] at river
  by_cases last : j.val = k+1
  · have atLast : j = Fin.last (k+1) := Fin.ext last
    rw [atLast]
    rcases main_target river with h | finish
    · exact h
    · let a := Fin.last k
      have atEnd : a.succ = Fin.last (k+1) := Fin.ext rfl
      have edge := b.arcStep a
      rw [atEnd,finish] at edge
      exact (b.river_ne_arc a (riverMain.trans (to_finish edge).symm)).elim
  · let next : Fin (k+1) := ⟨j.val,by omega⟩
    have nextStart : next.castSucc = j := Fin.ext rfl
    obtain ⟨i, label⟩ := bridge_arcs_main b riverMain next
    have edge := b.arcStep next
    rw [nextStart,label] at edge
    rcases main_source edge with old | start
    · exact old
    · by_cases zero : j.val = 0
      · have atZero : j = 0 := Fin.ext zero
        rw [atZero] at start
        have step := b.riverStep
        rw [start] at step
        exact (b.river_ne_arc next ((from_start step).trans label.symm)).elim
      · let prev : Fin (k+1) := ⟨j.val-1,by omega⟩
        have prevEnd : prev.succ = j := Fin.ext (by change (j.val-1)+1 = j.val; omega)
        have step := b.arcStep prev
        rw [prevEnd,start] at step
        obtain ⟨q,hl⟩ := bridge_arcs_main b riverMain prev
        have clash := hl.symm.trans (to_start step)
        cases clash

/-- Adding private endpoints and a two-arc return from each end to its start
preserves the exclusion of full bridges of every size. -/
private theorem returnBefore_fullFree (free : ∀ k, IsEmpty (Bridge before k)) :
    ∀ k, IsEmpty (Bridge (ReturnBefore before inside) k) := by
  classical
  intro k
  refine ⟨fun b => ?_⟩
  obtain ⟨r, riverMain⟩ := bridge_river_main b
  let oldVertex j := Classical.choose (bridge_vertices_original b riverMain j)
  let oldArc i := Classical.choose (bridge_arcs_main b riverMain i)
  have vert j : b.vertex j = .original (oldVertex j) := Classical.choose_spec (bridge_vertices_original b riverMain j)
  have arc i : b.arc i = .main (oldArc i) := Classical.choose_spec (bridge_arcs_main b riverMain i)
  apply (free k).false
  refine ⟨oldVertex,oldArc,r,?_,?_,?_,?_,?_⟩
  · intro a c h
    exact b.distinctVertices ((vert a).trans ((congrArg ReturnVertex.original h).trans (vert c).symm))
  · intro a c h
    exact b.distinctArcs ((arc a).trans ((congrArg ReturnPath.main h).trans (arc c).symm))
  · intro a h
    exact b.river_ne_arc a (riverMain.trans ((congrArg ReturnPath.main h).trans (arc a).symm))
  · have step := b.riverStep
    rw [riverMain,vert,vert] at step
    exact compared step
  · intro a
    have step := b.arcStep a
    rw [arc,vert,vert] at step
    exact compared step

end ReturnBefore


/-- Extend each path with private endpoints and add two paths to return
from its end to its start through a private intermediate vertex. -/
def returnPaths {V I : Type*} (paths : I → List V) : ReturnPath I → List (ReturnVertex V I)
  | .main i => .start i :: ((paths i).map ReturnVertex.original ++ [.finish i])
  | .first i => [.finish i, .turn i]
  | .second i => [.turn i, .start i]

local notation "ListBefore" => BeforeIn

section ListOrder

variable {V I : Type*} [DecidableEq V] [DecidableEq I]
variable (paths : I → List V)

private theorem idxOf_original_map (l : List V) (v : V) :
    ((l.map ReturnVertex.original : List (ReturnVertex V I))).idxOf (.original v) = l.idxOf v := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    by_cases same : w = v
    · subst w
      simp
    · simp only [List.map_cons, List.idxOf_cons_ne _ same,
        List.idxOf_cons_ne _ (show (ReturnVertex.original w : ReturnVertex V I) ≠ .original v from
          fun h => same (ReturnVertex.original.inj h)), ih]

private theorem returnPaths_idx_start (i : I) :
    (returnPaths paths (.main i)).idxOf (.start i) = 0 := by simp [returnPaths]

private theorem returnPaths_idx_finish (i : I) :
    (returnPaths paths (.main i)).idxOf (.finish i) = (paths i).length + 1 := by
  have absent : (ReturnVertex.finish i : ReturnVertex V I) ∉ (paths i).map ReturnVertex.original := by simp
  have apart : (ReturnVertex.start i : ReturnVertex V I) ≠ .finish i := by intro h; cases h
  simp only [returnPaths, List.idxOf_cons_ne _ apart, List.idxOf_append_of_notMem absent,
    List.length_map, List.idxOf_cons_self, Nat.add_zero, Nat.succ_eq_add_one]

private theorem returnPaths_idx_original (i : I) {v : V} (mem : v ∈ paths i) :
    (returnPaths paths (.main i)).idxOf (.original v) = (paths i).idxOf v + 1 := by
  have present : (ReturnVertex.original v : ReturnVertex V I) ∈ (paths i).map ReturnVertex.original :=
    List.mem_map_of_mem mem
  have apart : (ReturnVertex.start i : ReturnVertex V I) ≠ .original v := by intro h; cases h
  simp only [returnPaths, List.idxOf_cons_ne _ apart, List.idxOf_append_of_mem present,
    idxOf_original_map, Nat.succ_eq_add_one]

omit [DecidableEq V] [DecidableEq I] in
private theorem returnPaths_main_mem {i : I} {w : ReturnVertex V I}
    (mem : w ∈ returnPaths paths (.main i)) :
    w = .start i ∨ (∃ x ∈ paths i, w = .original x) ∨ w = .finish i := by
  simp only [returnPaths, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at mem
  rcases mem with start | ⟨x,hx,rfl⟩ | finish
  · exact Or.inl start
  · exact Or.inr (Or.inl ⟨x,hx,rfl⟩)
  · exact Or.inr (Or.inr finish)

private theorem two_vertex_before {p : ReturnPath I} {a b x y : ReturnVertex V I}
    (eq : returnPaths paths p = [a,b]) (ne : a ≠ b) (step : ListBefore (returnPaths paths) p x y) :
    x = a ∧ y = b := by
  obtain ⟨hx,hy,order⟩ := step
  rw [eq] at hx hy order
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (Nat.lt_irrefl _ order).elim
  · exact ⟨rfl,rfl⟩
  · simp [List.idxOf_cons_ne _ ne, List.idxOf_cons_self] at order
  · exact (Nat.lt_irrefl _ order).elim

private theorem returnPaths_before {p : ReturnPath I} {x y : ReturnVertex V I}
    (step : ListBefore (returnPaths paths) p x y) :
    ReturnBefore (ListBefore paths) (fun i v => v ∈ paths i) p x y := by
  cases p with
  | first i =>
    obtain ⟨rfl,rfl⟩ := two_vertex_before paths rfl (by intro h; cases h) step
    exact .first i
  | second i =>
    obtain ⟨rfl,rfl⟩ := two_vertex_before paths rfl (by intro h; cases h) step
    exact .second i
  | main i =>
    obtain ⟨hx,hy,order⟩ := step
    rcases returnPaths_main_mem paths hx with rfl | ⟨a, ha, rfl⟩ | rfl
    · rcases returnPaths_main_mem paths hy with rfl | ⟨b, hb, rfl⟩ | rfl
      · exact (Nat.lt_irrefl _ order).elim
      · exact .fromStart hb
      · exact .through i
    · rcases returnPaths_main_mem paths hy with rfl | ⟨b, hb, rfl⟩ | rfl
      · rw [returnPaths_idx_start paths] at order
        omega
      · rw [returnPaths_idx_original paths i ha, returnPaths_idx_original paths i hb] at order
        exact .original ⟨ha,hb,by omega⟩
      · exact .toFinish ha
    · rcases returnPaths_main_mem paths hy with rfl | ⟨b, hb, rfl⟩ | rfl
      · rw [returnPaths_idx_start paths] at order
        omega
      · rw [returnPaths_idx_finish paths, returnPaths_idx_original paths i hb] at order
        have lt := List.idxOf_lt_length_of_mem hb
        omega
      · exact (Nat.lt_irrefl _ order).elim

/-- The endpoint extensions and return paths preserve full exclusion at every size. -/
theorem returnPaths_fullFree (free : ∀ k, IsEmpty (Bridge (ListBefore paths) k)) :
    ∀ k, IsEmpty (Bridge (ListBefore (returnPaths paths)) k) := by
  intro k
  refine ⟨fun b => ?_⟩
  exact (ReturnBefore.returnBefore_fullFree (inside := fun i v => v ∈ paths i) free k).false
    (b.mapVertices id Function.injective_id (fun _ _ _ step => returnPaths_before paths step))

end ListOrder


section ConsecutiveOverlay

open Finset Relation

private def consecutiveListArcs {W : Type*} [DecidableEq W] : List W → Arcs W
  | [] => ∅
  | a::rest => match rest with
    | [] => ∅
    | b::_ => insert (a,b) (consecutiveListArcs rest)

private theorem reach_consecutiveList_end {W : Type*} [DecidableEq W] (a t : W) (L : List W) :
    Reach (consecutiveListArcs (a::(L ++ [t]))) a t := by
  induction L generalizing a with
  | nil => exact .single (by simp [Edge,consecutiveListArcs])
  | cons b rest ih =>
    change Reach (insert (a,b) (consecutiveListArcs (b::(rest ++ [t])))) a t
    exact (reach_mono (subset_insert _ _) (ih b)).head (mem_insert_self _ _)

/-- The edges between consecutive vertices of the extended paths. -/
def returnedOverlay {V I : Type*} [DecidableEq V] [DecidableEq I] [Fintype I]
    (paths : I → List V) : Arcs (ReturnVertex V I) :=
  univ.biUnion (fun i => consecutiveListArcs (returnPaths paths i))

private theorem returnVertex_card {V I : Type*} [Fintype V] [Fintype I] :
    Fintype.card (ReturnVertex V I) = Fintype.card V + 3*Fintype.card I := by
  let e : ReturnVertex V I ≃ V ⊕ (I ⊕ (I ⊕ I)) :=
    { toFun := fun v => match v with
        | .original x => .inl x
        | .start i => .inr (.inl i)
        | .finish i => .inr (.inr (.inl i))
        | .turn i => .inr (.inr (.inr i))
      invFun := fun v => match v with
        | .inl x => .original x
        | .inr (.inl i) => .start i
        | .inr (.inr (.inl i)) => .finish i
        | .inr (.inr (.inr i)) => .turn i
      left_inv := by rintro (x|i|i|i) <;> rfl
      right_inv := by rintro (x|i|i|i) <;> rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_sum]
  omega

/-- The endpoint demands in the returned overlay admit the two SCC connector
forests, independent of the path incidence count. -/
private theorem returnedOverlay_small {V I : Type*} [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype I]
    (paths : I → List V) :
    ∃ H ⊆ returnedOverlay paths, H.card ≤ 2*(Fintype.card V+3*Fintype.card I) ∧
      ∀ i, Reach H (.start i) (.finish i) ∧ Reach H (.finish i) (.turn i) ∧ Reach H (.turn i) (.start i) := by
  let value := Fintype.equivFin (ReturnVertex V I)
  let _ : LinearOrder (ReturnVertex V I) := LinearOrder.lift' value value.injective
  let G := returnedOverlay paths
  let H := connectors G
  refine ⟨H, connectors_subset G, (connectors_card G).trans_eq (by rw [returnVertex_card]), ?_⟩
  intro i
  have includes (c : ReturnPath I) : consecutiveListArcs (returnPaths paths c) ⊆ G :=
    fun _ h => mem_biUnion.mpr ⟨c,mem_univ c,h⟩
  have forward : Reach G (.start i) (.finish i) := reach_mono (includes (.main i))
    (reach_consecutiveList_end _ _ ((paths i).map ReturnVertex.original))
  have first : Reach G (.finish i) (.turn i) := .single (includes (.first i) (by simp [returnPaths,consecutiveListArcs]))
  have second : Reach G (.turn i) (.start i) := .single (includes (.second i) (by simp [returnPaths,consecutiveListArcs]))
  exact ⟨connectors_reach (componentLabel_eq.mpr ⟨forward,first.trans second⟩),
    connectors_reach (componentLabel_eq.mpr ⟨first,second.trans forward⟩),
    connectors_reach (componentLabel_eq.mpr ⟨second,forward.trans first⟩)⟩

end ConsecutiveOverlay


section EndpointDemands

open Finset

theorem returnPaths_nodup {V I : Type*} {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (c : ReturnPath I) : (returnPaths paths c).Nodup := by
  cases c with
  | first i => simp [returnPaths]
  | second i => simp [returnPaths]
  | main i =>
    apply List.nodup_cons.mpr
    refine ⟨by simp, ?_⟩
    have mapped : ((paths i).map (ReturnVertex.original : V → ReturnVertex V I)).Nodup :=
      (simple i).map (fun _ _ same => ReturnVertex.original.inj same)
    refine mapped.append (by simp) ?_
    intro w hw last
    simp only [List.mem_singleton] at last
    subst w
    simp at hw

private def returnPathEquiv (I : Type*) : ReturnPath I ≃ I ⊕ (I ⊕ I) where
  toFun
    | .main i => .inl i
    | .first i => .inr (.inl i)
    | .second i => .inr (.inr i)
  invFun
    | .inl i => .main i
    | .inr (.inl i) => .first i
    | .inr (.inr i) => .second i
  left_inv := by rintro (i|i|i) <;> rfl
  right_inv := by rintro (i|i|i) <;> rfl

private theorem returnPath_card (I : Type*) [Fintype I] : Fintype.card (ReturnPath I) = 3*Fintype.card I := by
  rw [Fintype.card_congr (returnPathEquiv I)]
  simp only [Fintype.card_sum]
  omega

theorem returnPaths_mass {V I : Type*} [Fintype I] (paths : I → List V) :
    ∑ c, (returnPaths paths c).length = (∑ i, (paths i).length) + 6*Fintype.card I := by
  let e := returnPathEquiv I
  rw [← Equiv.sum_comp e.symm (fun c => (returnPaths paths c).length)]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  change (∑ i, (returnPaths paths (.main i)).length) +
    ((∑ i, (returnPaths paths (.first i)).length) + ∑ i, (returnPaths paths (.second i)).length) = _
  simp only [returnPaths, List.length_cons, List.length_nil, List.length_append, List.length_map,
    Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Finset.card_univ]
  omega

private def returnedDemand {V I : Type*} : ReturnPath I → ReturnVertex V I × ReturnVertex V I
  | .main i => (.start i,.finish i)
  | .first i => (.finish i,.turn i)
  | .second i => (.turn i,.start i)

/-- The first and last vertex of each extended path, in the order of the finite enumeration. -/
noncomputable def returnedDemands (V I : Type*) [Fintype I] : List (ReturnVertex V I × ReturnVertex V I) :=
  (univ : Finset (ReturnPath I)).toList.map returnedDemand

private theorem returnedDemand_injective (V I : Type*) :
    Function.Injective (returnedDemand : ReturnPath I → ReturnVertex V I × ReturnVertex V I) := by
  rintro (i|i|i) (j|j|j) same <;>
    have left := congrArg Prod.fst same <;> simp_all [returnedDemand]

theorem returnedDemands_nodup (V I : Type*) [Fintype I] : (returnedDemands V I).Nodup :=
  (Finset.nodup_toList _).map (returnedDemand_injective V I)

theorem returnedDemands_length (V I : Type*) [Fintype I] :
    (returnedDemands V I).length = 3*Fintype.card I := by
  simp [returnedDemands, returnPath_card]

theorem returnPaths_length_pos {V I : Type*} (paths : I → List V) (i : ReturnPath I) :
    0 < (returnPaths paths i).length := by cases i <;> simp [returnPaths]

/-- Two SCC connector forests serve every endpoint demand in the overlay. -/
theorem returnedOverlay_preserver {V I : Type*} [DecidableEq V] [DecidableEq I] [Fintype V] [Fintype I]
    (paths : I → List V) :
    ∃ H ⊆ returnedOverlay paths, H.card ≤ 2*(Fintype.card V+3*Fintype.card I) ∧
      Preserves (returnedOverlay paths) H (returnedDemands V I) := by
  obtain ⟨H,subset,size,reach⟩ := returnedOverlay_small paths
  refine ⟨H,subset,size,?_⟩
  intro d present
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp present
  refine ⟨reach_mono subset,fun _ => ?_⟩
  cases c with
  | main i => exact (reach i).1
  | first i => exact (reach i).2.1
  | second i => exact (reach i).2.2

end EndpointDemands

end OnlineReachabilityPreservers.SourceAudit
