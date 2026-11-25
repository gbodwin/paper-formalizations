import OnlineReachabilityPreservers.AssignmentListRouteWork
import OnlineReachabilityPreservers.SteinerCuts

/-! Exact demand-interval searches on explicit arc lists. -/

namespace OnlineReachabilityPreservers

open Finset

private def filterListWithWordWork {A : Type*} (test : A → Bool × ℕ) : List A → List A × ℕ
  | [] => ([],2)
  | a :: tail =>
    let accepted := test a
    let rest := filterListWithWordWork test tail
    ((if accepted.1 then a :: rest.1 else rest.1),accepted.2+rest.2+10)

private theorem filterListWithWordWork_shape {A : Type*} (test : A → Bool × ℕ) (rows : List A) :
    (filterListWithWordWork test rows).1 = rows.filter (fun a => (test a).1) := by
  induction rows with
  | nil => rfl
  | cons a tail ih => simp only [filterListWithWordWork,List.filter_cons,ih]

private theorem filterListWithWordWork_spec {A : Type*} (test : A → Bool × ℕ)
    (rows : List A) (B : ℕ) (each : ∀ a ∈ rows, (test a).2 ≤ B) :
    let out := filterListWithWordWork test rows
    out.1 = rows.filter (fun a => (test a).1) ∧ out.2 ≤ rows.length*(B+10)+2 := by
  induction rows with
  | nil => simp [filterListWithWordWork]
  | cons a tail ih =>
    have work := (ih (fun a ha => each a (List.mem_cons_of_mem _ ha))).2
    have head := each a List.mem_cons_self
    refine ⟨filterListWithWordWork_shape _ _,?_⟩
    · change (test a).2+(filterListWithWordWork test tail).2+10 ≤ (tail.length+1)*(B+10)+2
      rw [Nat.add_mul,Nat.one_mul]
      omega

private theorem filterListWithWordWork_nodup {A : Type*} (test : A → Bool × ℕ)
    (rows : List A) (simple : rows.Nodup) : (filterListWithWordWork test rows).1.Nodup := by
  rw [filterListWithWordWork_shape]
  exact simple.filter _

private theorem filterListWithWordWork_tally {A : Type*} (test : A → Bool × ℕ) (rows : List A) :
    (filterListWithWordWork test rows).2 = 2+(rows.map fun a => (test a).2+10).sum := by
  induction rows with
  | nil => rfl
  | cons a tail ih =>
    simp only [filterListWithWordWork,List.map_cons,List.sum_cons,ih]
    omega

private def filterMultisetWithWordWork {A : Type*} (test : A → Bool × ℕ) (rows : Multiset A) : Multiset A × ℕ :=
  Quotient.lift (fun list => let result := filterListWithWordWork test list; (↑result.1,result.2))
    (by
      intro a b perm
      refine Prod.ext ?_ ?_
      · simp only [filterListWithWordWork_shape]
        exact Quotient.sound (perm.filter _)
      · simp only [filterListWithWordWork_tally,(perm.map _).sum_eq]) rows

private theorem filterMultisetWithWordWork_spec {A : Type*} (test : A → Bool × ℕ) (rows : Multiset A) :
    let out := filterMultisetWithWordWork test rows
    out.1 = rows.filter (fun a => (test a).1) ∧
      ∀ B, (∀ a ∈ rows, (test a).2 ≤ B) → out.2 ≤ rows.card*(B+10)+2 := by
  refine Quotient.inductionOn rows ?_
  intro explicit
  constructor
  · have predicate : (fun b => decide ((test b).1 = true)) = (fun b => (test b).1) := by
      funext b
      cases (test b).1 <;> simp
    change ((filterListWithWordWork test explicit).1 : Multiset A) =
      ↑(explicit.filter (fun b => decide ((test b).1 = true)))
    rw [predicate,filterListWithWordWork_shape]
  · intro B bound
    exact (filterListWithWordWork_spec test explicit B bound).2

/-- Filter the underlying rows once and charge the supplied test on each row. -/
def filterFinsetWithWordWork {A : Type*} (test : A → Bool × ℕ) (rows : Finset A) : Finset A × ℕ :=
  let out := filterMultisetWithWordWork test rows.val
  have simple : out.1.Nodup := (filterMultisetWithWordWork_spec test rows.val).1.symm ▸ (rows.filter fun a => (test a).1).nodup
  (⟨out.1,simple⟩,out.2)

theorem filterFinsetWithWordWork_spec {A : Type*} (test : A → Bool × ℕ) (rows : Finset A) :
    let out := filterFinsetWithWordWork test rows
    out.1 = rows.filter (fun a => (test a).1) ∧
      ∀ B, (∀ a ∈ rows, (test a).2 ≤ B) → out.2 ≤ rows.card*(B+10)+2 := by
  obtain ⟨same,work⟩ := filterMultisetWithWordWork_spec test rows.val
  exact ⟨eq_of_veq same,work⟩

private def finiteSetOfRows {A : Type*} (rows : List A) (simple : rows.Nodup) : Finset A :=
  ⟨(rows : Multiset A),by simpa using simple⟩

@[simp] private theorem mem_finiteSetOfRows {A : Type*} {rows : List A} {simple : rows.Nodup} {a : A} :
    a ∈ finiteSetOfRows rows simple ↔ a ∈ rows := Iff.rfl

private theorem finiteSetOfRows_eq_toFinset {A : Type*} [DecidableEq A] (rows : List A) (simple : rows.Nodup) :
    finiteSetOfRows rows simple = rows.toFinset := by
  ext a
  simp

variable {V : Type*} [LinearOrder V] [Fintype V]

private def bothEndpointsInWithWordWork (vertices : List V) (e : V × V) : Bool × ℕ :=
  let src := memScanWithWordWork e.1 vertices
  let dst := memScanWithWordWork e.2 vertices
  (src.1 && dst.1,src.2+dst.2+5)

omit [Fintype V] in
private theorem bothEndpointsInWithWordWork_spec (vertices : List V) (e : V × V) :
    let out := bothEndpointsInWithWordWork vertices e
    out.1 = decide (e.1 ∈ vertices ∧ e.2 ∈ vertices) ∧ out.2 ≤ 4*vertices.length+7 := by
  obtain ⟨left,leftWork⟩ := memScanWithWordWork_spec e.1 vertices
  obtain ⟨right,rightWork⟩ := memScanWithWordWork_spec e.2 vertices
  refine ⟨?_,?_⟩
  · by_cases l : e.1 ∈ vertices <;> by_cases r : e.2 ∈ vertices <;>
      simp [bothEndpointsInWithWordWork,left,right,l,r]
  · change (memScanWithWordWork e.1 vertices).2+(memScanWithWordWork e.2 vertices).2+5 ≤ _
    omega

/-- Demand interval vertices and its induced arc list, with no repetitions. -/
structure DemandIntervalRows (V : Type*) where
  vertices : {rows : List V // rows.Nodup}
  arcs : {rows : List (V × V) // rows.Nodup}

def DemandIntervalRows.vertexSet (interval : DemandIntervalRows V) : Finset V :=
  finiteSetOfRows interval.vertices.val interval.vertices.property

def DemandIntervalRows.arcSet (interval : DemandIntervalRows V) : Arcs V :=
  finiteSetOfRows interval.arcs.val interval.arcs.property

/-- Make the two reach lists, intersect their vertices and filter the original arc rows. -/
def demandIntervalRowsWithWordWork (arcs : {rows : List (V × V) // rows.Nodup}) (d : V × V) (depth : ℕ) :
    DemandIntervalRows V × ℕ :=
  let reversed := arcs.val.map Prod.swap
  let fromSource := reachInListWithWordWork reversed d.1 depth
  let toTarget := reachInListWithWordWork arcs.val d.2 depth
  let interval := filterListWithWordWork (fun x => memScanWithWordWork x toTarget.1) fromSource.1
  let edges := filterListWithWordWork (bothEndpointsInWithWordWork interval.1) arcs.val
  let vertices := ⟨interval.1,filterListWithWordWork_nodup _ _
    (reachInListWithWordWork_spec reversed d.1 depth).1⟩
  let paired := ⟨edges.1,filterListWithWordWork_nodup _ _ arcs.property⟩
  (⟨vertices,paired⟩,fromSource.2+toTarget.2+7*arcs.val.length+interval.2+edges.2+12)

def demandIntervalRowsWordBudget (n m : ℕ) : ℕ :=
  2*reachInListWordBudget n m+7*m+n*(2*n+11)+m*(4*n+17)+16

theorem demandIntervalRowsWithWordWork_spec (arcs : {rows : List (V × V) // rows.Nodup}) (d : V × V) :
    let out := demandIntervalRowsWithWordWork arcs d (Fintype.card V)
    out.1.vertexSet = reachInterval arcs.val.toFinset d ∧ out.1.arcSet = intervalArcs arcs.val.toFinset d ∧
      out.1.vertices.val.length ≤ Fintype.card V ∧ out.1.arcs.val.length ≤ arcs.val.length ∧
      out.2 ≤ demandIntervalRowsWordBudget (Fintype.card V) arcs.val.length := by
  let n := Fintype.card V
  let reverse := arcs.val.map Prod.swap
  let fromSource := reachInListWithWordWork reverse d.1 n
  let toTarget := reachInListWithWordWork arcs.val d.2 n
  let interval := filterListWithWordWork (fun x => memScanWithWordWork x toTarget.1) fromSource.1
  let edges := filterListWithWordWork (bothEndpointsInWithWordWork interval.1) arcs.val
  obtain ⟨sourceSimple,sourceSet,sourceWork⟩ := reachInListWithWordWork_spec reverse d.1 n
  obtain ⟨targetSimple,targetSet,targetWork⟩ := reachInListWithWordWork_spec arcs.val d.2 n
  have sourceSize : fromSource.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup sourceSimple]
    exact card_le_univ _
  have targetSize : toTarget.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup targetSimple]
    exact card_le_univ _
  obtain ⟨intervalList,intervalWork⟩ := filterListWithWordWork_spec (fun x => memScanWithWordWork x toTarget.1)
    fromSource.1 (2*n+1) (fun x _ => (memScanWithWordWork_spec x toTarget.1).2.trans (by gcongr))
  have intervalSize : interval.1.length ≤ n := by
    change interval.1 = _ at intervalList
    rw [intervalList]
    exact (List.length_filter_le _ _).trans sourceSize
  obtain ⟨edgeList,edgeWork⟩ := filterListWithWordWork_spec (bothEndpointsInWithWordWork interval.1) arcs.val
    (4*n+7) (fun a _ => (bothEndpointsInWithWordWork_spec interval.1 a).2.trans (by gcongr))
  have reverseExact : reverse.toFinset = reverseArcs arcs.val.toFinset := by
    ext e
    simp [reverse, reverseArcs, List.mem_toFinset,mem_image]
  have intervalExact : interval.1.toFinset = reachInterval arcs.val.toFinset d := by
    change interval.1 = _ at intervalList
    rw [intervalList]
    ext v
    simp only [List.mem_toFinset,List.mem_filter,(memScanWithWordWork_spec v toTarget.1).1,decide_eq_true_eq,
      reachInterval,mem_inter]
    rw [← List.mem_toFinset,sourceSet, ← List.mem_toFinset,targetSet, reverseExact]
    rfl
  have edgeExact : edges.1.toFinset = intervalArcs arcs.val.toFinset d := by
    change edges.1 = _ at edgeList
    rw [edgeList]
    ext e
    simp only [List.mem_toFinset,List.mem_filter,(bothEndpointsInWithWordWork_spec interval.1 e).1,decide_eq_true_eq,
      intervalArcs,mem_filter]
    have membership (v : V) : v ∈ interval.1 ↔ v ∈ reachInterval arcs.val.toFinset d := by
      rw [← intervalExact]
      exact List.mem_toFinset.symm
    rw [membership, membership]
  refine ⟨?_,?_,intervalSize,?_,?_⟩
  · exact (finiteSetOfRows_eq_toFinset interval.1 _).trans intervalExact
  · exact (finiteSetOfRows_eq_toFinset edges.1 _).trans edgeExact
  · change edges.1.length ≤ arcs.val.length
    change edges.1 = _ at edgeList
    rw [edgeList]
    exact List.length_filter_le _ _
  · have rs : reverse.length = arcs.val.length := by simp [reverse]
    rw [rs] at sourceWork
    change fromSource.2+toTarget.2+7*arcs.val.length+interval.2+edges.2+12 ≤ _
    have intervalCost : interval.2 ≤ n*(2*n+11)+2 := intervalWork.trans (by gcongr)
    change _ ≤ 2*reachInListWordBudget n arcs.val.length+7*arcs.val.length+
      n*(2*n+11)+arcs.val.length*(4*n+17)+16
    change fromSource.2 ≤ reachInListWordBudget n arcs.val.length at sourceWork
    change toTarget.2 ≤ reachInListWordBudget n arcs.val.length at targetWork
    change edges.2 ≤ arcs.val.length*(4*n+17)+2 at edgeWork
    omega

/-- Restrict the residual source side to the original demand's interval. -/
def intersectWithIntervalRowsWithWordWork (interval : DemandIntervalRows V) (side : Finset V) : Finset V × ℕ :=
  filterFinsetWithWordWork (fun v => memScanWithWordWork v interval.vertices.val) side

omit [Fintype V] in
theorem intersectWithIntervalRowsWithWordWork_spec (interval : DemandIntervalRows V) (side : Finset V) :
    let out := intersectWithIntervalRowsWithWordWork interval side
    out.1 = side ∩ interval.vertexSet ∧ out.2 ≤ side.card*(2*interval.vertices.val.length+11)+2 := by
  obtain ⟨same,work⟩ := filterFinsetWithWordWork_spec (fun v => memScanWithWordWork v interval.vertices.val) side
  refine ⟨?_,?_⟩
  · change (filterFinsetWithWordWork (fun v => memScanWithWordWork v interval.vertices.val) side).1 = _
    rw [same]
    ext v
    simp [DemandIntervalRows.vertexSet,(memScanWithWordWork_spec v interval.vertices.val).1]
  · exact work (2*interval.vertices.val.length+1) (fun v _ => (memScanWithWordWork_spec v interval.vertices.val).2)

private def memFinsetWithWordWork {A : Type*} [DecidableEq A] (key : A) (rows : Finset A) : Bool × ℕ :=
  let hit := filterFinsetWithWordWork (fun v => (decide (v = key),2)) rows
  (decide hit.1.Nonempty,hit.2+4)

private theorem memFinsetWithWordWork_spec {A : Type*} [DecidableEq A] (key : A) (rows : Finset A) :
    let out := memFinsetWithWordWork key rows
    out.1 = decide (key ∈ rows) ∧ out.2 ≤ 12*rows.card+6 := by
  obtain ⟨shape,charged⟩ := filterFinsetWithWordWork_spec (fun v => (decide (v = key),2)) rows
  refine ⟨?_,?_⟩
  · change decide ((filterFinsetWithWordWork (fun v => (decide (v = key),2)) rows).1.Nonempty) = _
    rw [shape]
    have present : (rows.filter (fun a => decide (a = key))).Nonempty ↔ key ∈ rows := by
      simp only [Finset.Nonempty,mem_filter,decide_eq_true_eq]
      exact ⟨fun ⟨v,mem,same⟩ => same ▸ mem,fun h => ⟨key,h,rfl⟩⟩
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using present
  · have used := charged 2 (fun _ _ => le_rfl)
    change (filterFinsetWithWordWork (fun v => (decide (v = key),2)) rows).2+4 ≤ _
    omega

private def outwardEndpointTestWithWordWork (side : Finset V) (arc : V × V) : Bool × ℕ :=
  let tail := memFinsetWithWordWork arc.1 side
  let head := memFinsetWithWordWork arc.2 side
  (tail.1 && !head.1,tail.2+head.2+5)

omit [Fintype V] in
private theorem outwardEndpointTestWithWordWork_spec (side : Finset V) (arc : V × V) :
    let out := outwardEndpointTestWithWordWork side arc
    out.1 = decide (arc.1 ∈ side ∧ arc.2 ∉ side) ∧ out.2 ≤ 24*side.card+17 := by
  obtain ⟨tail,tailCost⟩ := memFinsetWithWordWork_spec arc.1 side
  obtain ⟨head,headCost⟩ := memFinsetWithWordWork_spec arc.2 side
  refine ⟨?_,?_⟩
  · by_cases l : arc.1 ∈ side <;> by_cases r : arc.2 ∈ side <;>
      simp [outwardEndpointTestWithWordWork,tail,head,l,r]
  · change (memFinsetWithWordWork arc.1 side).2+(memFinsetWithWordWork arc.2 side).2+5 ≤ _
    omega

/-- Apply the cut to the prepared interval arcs with the membership work charged. -/
def outgoingCutFromIntervalRowsWithWordWork (interval : DemandIntervalRows V) (side : Finset V) : Arcs V × ℕ :=
  filterFinsetWithWordWork (outwardEndpointTestWithWordWork side) interval.arcSet

omit [Fintype V] in
theorem outgoingCutFromIntervalRowsWithWordWork_spec (interval : DemandIntervalRows V) (side : Finset V) :
    let out := outgoingCutFromIntervalRowsWithWordWork interval side
    out.1 = outgoingCut interval.arcSet side ∧ out.2 ≤ interval.arcSet.card*(24*side.card+27)+2 := by
  obtain ⟨same,spent⟩ := filterFinsetWithWordWork_spec (outwardEndpointTestWithWordWork side) interval.arcSet
  refine ⟨?_,?_⟩
  · unfold outgoingCutFromIntervalRowsWithWordWork
    rw [same]
    ext e
    simp [outgoingCut,(outwardEndpointTestWithWordWork_spec side e).1]
  · exact spent (24*side.card+17) (fun e _ => (outwardEndpointTestWithWordWork_spec side e).2)

end OnlineReachabilityPreservers
