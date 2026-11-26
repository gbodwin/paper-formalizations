import OnlineReachabilityPreservers.PathAssignments
import OnlineReachabilityPreservers.SccLiftListWork

/-! Exact list-backed routing in the hop-decreasing subgraph, with operation counts. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def routeEdgeWithWordWork (G : List (V × V)) (t : V) (depth : ℕ) (e : V × V) :
    ((V × V) × Bool) × ℕ :=
  let source := hopsListWithWordWork G e.1 t depth
  let target := hopsListWithWordWork G e.2 t depth
  ((e,decide (target.1 < source.1)),source.2+target.2+7)

private theorem routeEdgeWithWordWork_spec (G : List (V × V)) (t : V) (e : V × V) :
    let n := Fintype.card V
    let out := routeEdgeWithWordWork G t n e
    out.1 = (e,decide (hops G.toFinset e.2 t < hops G.toFinset e.1 t)) ∧
      out.2 ≤ 2*(hopsListWordBudget n G.length)+7 := by
  obtain ⟨source, sourceWork⟩ := hopsListWithWordWork_spec G e.1 t
  obtain ⟨target, targetWork⟩ := hopsListWithWordWork_spec G e.2 t
  constructor
  · simp only [routeEdgeWithWordWork, source, target]
  · exact (Nat.add_le_add_right (Nat.add_le_add sourceWork targetWork) 7).trans_eq (by rw [two_mul])

private def routeArcsListWithWordWork (G : List (V × V)) (t : V) (depth : ℕ) : List (V × V) × ℕ :=
  let tested := mapListWithChecks (routeEdgeWithWordWork G t depth) G
  let keep := tested.1.filter Prod.snd
  (keep.map Prod.fst, tested.2+19*G.length+8)

private def routeArcsListWordBudget (n m : ℕ) : ℕ := m*(2*(hopsListWordBudget n m)+26)+8

private theorem routeArcsListWithWordWork_spec (G : List (V × V)) (t : V) :
    let n := Fintype.card V
    let out := routeArcsListWithWordWork G t n
    out.1.toFinset = G.toFinset.filter (fun e => hops G.toFinset e.2 t < hops G.toFinset e.1 t) ∧
      out.1.length ≤ G.length ∧ out.2 ≤ routeArcsListWordBudget n G.length := by
  let n := Fintype.card V
  let annotate (e : V × V) := (e,decide (hops G.toFinset e.2 t < hops G.toFinset e.1 t))
  let tested := mapListWithChecks (routeEdgeWithWordWork G t n) G
  obtain ⟨same, work⟩ := mapListWithChecks_spec (routeEdgeWithWordWork G t n) annotate G
    (2*(hopsListWordBudget n G.length)+7)
    (fun e _ => (routeEdgeWithWordWork_spec G t e).1)
    (fun e _ => (routeEdgeWithWordWork_spec G t e).2)
  change tested.1 = G.map annotate at same
  refine ⟨?_,?_,?_⟩
  · change ((tested.1.filter Prod.snd).map Prod.fst).toFinset = _
    rw [same]
    ext e
    simp [annotate, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨a, b, ⟨on, rfl⟩, steps⟩
      exact ⟨on, steps⟩
    · rintro ⟨on, steps⟩
      exact ⟨e.1,e.2,⟨on,rfl⟩,steps⟩
  · change ((tested.1.filter Prod.snd).map Prod.fst).length ≤ G.length
    rw [same, List.length_map]
    simpa only [List.length_map] using List.length_filter_le Prod.snd (G.map annotate)
  · change tested.2+19*G.length+8 ≤ _
    exact (Nat.add_le_add_right (Nat.add_le_add_right work _) _).trans_eq (by unfold routeArcsListWordBudget; ring)

/-- Use the exact hop-decreasing filtered network before growing the route.
The tally includes two hop searches for each tested edge. -/
def routePathListWithWordWork (G : List (V × V)) (s t : V) (depth : ℕ) :
    Option (List (V × V)) × ℕ :=
  let selected := routeArcsListWithWordWork G t depth
  let result := forwardPathListWithWordWork selected.1 [] s t depth
  (result.1, selected.2+result.2+4)

def routePathListWordBudget (n m : ℕ) : ℕ :=
  routeArcsListWordBudget n m+reachInListWordBudget n m+(n+1)*(17+n*(2*m+20))+8

theorem routePathListWordBudget_le {n n' m m' : ℕ} (vertices : n ≤ n') (arcs : m ≤ m') :
    routePathListWordBudget n m ≤ routePathListWordBudget n' m' := by
  unfold routePathListWordBudget routeArcsListWordBudget hopsListWordBudget reachInListWordBudget
  gcongr

theorem routePathListWordBudget_mono_arcs (n : ℕ) : Monotone (routePathListWordBudget n) :=
  fun _ _ short => routePathListWordBudget_le le_rfl short

theorem routePathListWithWordWork_spec (G : List (V × V)) (s t : V) :
    let n := Fintype.card V
    let out := routePathListWithWordWork G s t n
    out.1 = routePath G.toFinset s t ∧ out.2 ≤ routePathListWordBudget n G.length := by
  let n := Fintype.card V
  let selected := routeArcsListWithWordWork G t n
  let result := forwardPathListWithWordWork selected.1 [] s t n
  obtain ⟨selectedSet, len, cost⟩ := routeArcsListWithWordWork_spec G t
  obtain ⟨same, work, _⟩ := forwardPathListWithWordWork_spec selected.1 [] s t
  constructor
  · change result.1 = _
    rw [show result.1 = _ from same, show selected.1.toFinset = _ from selectedSet]
    rfl
  · have charged : result.2 ≤ reachInListWordBudget n G.length+(n+1)*(17+n*(2*G.length+20))+4 := by
      apply work.trans
      simp only [List.length_nil, Nat.add_zero]
      unfold reachInListWordBudget
      gcongr
    exact (Nat.add_le_add_right (Nat.add_le_add cost charged) 4).trans_eq (by unfold routePathListWordBudget; ring)

/-- The selected lift is simple even when the quotient option is absent. -/
theorem liftPath_length_le (G : Arcs V) (d : V × V) (p : Option (List (V × V))) :
    ((liftPath G d p).getD []).length ≤ Fintype.card V := by
  unfold liftPath
  cases chosen : routePath (connectors G ∪ liftedArcs G (pathArcs p)) d.1 d.2 with
  | none => simp
  | some path =>
    have distinct := (routePath_some chosen).2
    have bound := card_le_univ (path.map Prod.fst ++ [d.2]).toFinset
    rw [List.toFinset_card_of_nodup distinct, List.length_append, List.length_map, List.length_singleton] at bound
    exact (Nat.le_succ _).trans bound

theorem hopsWithSearchWork_count (G : Arcs V) (s t : V) :
    (hopsWithSearchWork G s t).2 = (∑ k ∈ range (Fintype.card V+1), k)*G.card := by
  let entry := fun k : ℕ => (k,decide (s ∈ (reachInWithArcInspections G t k).1),(reachInWithArcInspections G t k).2)
  change (∑ v ∈ (range (Fintype.card V+1)).image entry, v.2.2) = _
  rw [sum_image (fun _ _ _ _ eq => congrArg Prod.fst eq)]
  simp only [entry,reachInWithArcInspections_spec,sum_mul]

omit [Fintype V] in
theorem growFromWithSuccessorTests_successFee (G H : Arcs V) (R : Finset V) (t : V)
    (fuel : ℕ) (u : V) (path : List (V × V))
    (found : (growFromWithSuccessorTests G H R t fuel u).1 = some path) :
    (growFromWithSuccessorTests G H R t fuel u).2 = path.length*(2*R.card) := by
  induction fuel generalizing u path with
  | zero =>
    by_cases same : u = t
    · have empty : path = [] := by simpa [growFromWithSuccessorTests,same] using found.symm
      subst path
      simp [growFromWithSuccessorTests,same]
    · simp [growFromWithSuccessorTests,same] at found
  | succ fuel ih =>
    by_cases same : u = t
    · have empty : path = [] := by simpa [growFromWithSuccessorTests,same] using found.symm
      subst path
      simp [growFromWithSuccessorTests,same]
    cases step : nextVertex G H R u with
    | none => simp [growFromWithSuccessorTests,same,step] at found
    | some v =>
      let tail := growFromWithSuccessorTests G H R t fuel v
      cases routed : tail.1 with
      | none =>
        change (growFromWithSuccessorTests G H R t fuel v).1 = none at routed
        simp [growFromWithSuccessorTests,same,step,routed] at found
      | some suffix =>
        have work := ih v suffix routed
        change (growFromWithSuccessorTests G H R t fuel v).1 = some suffix at routed
        have eq : (u,v)::suffix = path := by
          simpa [growFromWithSuccessorTests,same,step,routed] using found
        subst path
        simp only [growFromWithSuccessorTests,same,ite_false,step,List.length_cons,work,Nat.add_mul,Nat.one_mul]

theorem growFromWithSuccessorTests_unreachableFee (G H : Arcs V) (sub : H ⊆ G) (s t : V)
    (unreachable : ¬ Reach G s t) :
    (growFromWithSuccessorTests G H (reaches G t) t (Fintype.card V) s).2 = 2*(reaches G t).card := by
  have unequal : s ≠ t := by
    intro same
    subst s
    exact unreachable .refl
  have noNext : nextVertex G H (reaches G t) s = none := by
    cases selected : nextVertex G H (reaches G t) s with
    | none => rfl
    | some v =>
      obtain ⟨arc,member,_⟩ := nextVertex_spec sub selected
      exact (unreachable ((mem_reaches.mp member).head arc)).elim
  have positive : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  cases count : Fintype.card V with
  | zero => omega
  | succ fuel => simp [growFromWithSuccessorTests,unequal,noNext]

theorem routePathWithSearchWork_fees (G : Arcs V) (s t : V) :
    let n := Fintype.card V
    let H := G.filter (fun e => hops G e.2 t < hops G e.1 t)
    let R := reaches H t
    let result := routePathWithSearchWork G s t
    let hopsVisits := (∑ k ∈ range (n+1), k)*G.card
    result.2.1 = G.card*(2*hopsVisits)+n*H.card ∧
      result.2.2 = ((result.1.map List.length).getD 1)*(2*R.card) := by
  let n := Fintype.card V
  let H := G.filter (fun e => hops G e.2 t < hops G e.1 t)
  let R := reaches H t
  let entry (e : V × V) :=
    let src := hopsWithSearchWork G e.1 t
    let dst := hopsWithSearchWork G e.2 t
    (e,decide (dst.1 < src.1),src.2+dst.2)
  let checked := G.image entry
  let kept := (checked.filter (fun r => r.2.1 = true)).image Prod.fst
  have pass (e : V × V) : (entry e).2.1 = true ↔ hops G e.2 t < hops G e.1 t := by
    simp [entry,(hopsWithSearchWork_spec G e.1 t).1,(hopsWithSearchWork_spec G e.2 t).1]
  have edges : kept = H := by
    ext e
    constructor
    · intro mem
      obtain ⟨r,hr,rfl⟩ := mem_image.mp mem
      obtain ⟨present,good⟩ := mem_filter.mp hr
      obtain ⟨a,ha,rfl⟩ := mem_image.mp present
      exact mem_filter.mpr ⟨ha,(pass a).mp good⟩
    · intro mem
      obtain ⟨given,good⟩ := mem_filter.mp mem
      exact mem_image.mpr ⟨entry e,mem_filter.mpr ⟨mem_image_of_mem _ given,(pass e).mpr good⟩,rfl⟩
  let total := (∑ k ∈ range (n+1), k)*G.card
  have sum : (∑ r ∈ checked, r.2.2) = G.card*(2*total) := by
    dsimp only [checked]
    rw [sum_image (fun _ _ _ _ eq => congrArg Prod.fst eq)]
    have fee (e : V × V) : (entry e).2.2 = 2*total := by
      change (hopsWithSearchWork G e.1 t).2+(hopsWithSearchWork G e.2 t).2 = _
      rw [hopsWithSearchWork_count,hopsWithSearchWork_count]
      ring
    simp only [fee,sum_const,nsmul_eq_mul,Nat.cast_id]
  let tail := forwardPathWithSearchWork H ∅ s t
  let grow := growFromWithSuccessorTests H ∅ R t n s
  have tailEq : tail = (grow.1,n*H.card,grow.2) := by
    simp [tail,forwardPathWithSearchWork,reachInWithArcInspections_spec,grow,R,reaches,n]
  have produced : (routePathWithSearchWork G s t).1 = grow.1 := by
    change (forwardPathWithSearchWork kept ∅ s t).1 = grow.1
    rw [edges,show forwardPathWithSearchWork H ∅ s t = tail from rfl,tailEq]
  refine ⟨?_,?_⟩
  · change (∑ r ∈ checked, r.2.2)+(forwardPathWithSearchWork kept ∅ s t).2.1 = _
    rw [sum,edges,show forwardPathWithSearchWork H ∅ s t = tail from rfl,tailEq]
  · change (forwardPathWithSearchWork kept ∅ s t).2.2 = _
    rw [edges,show forwardPathWithSearchWork H ∅ s t = tail from rfl,tailEq,produced]
    cases selected : grow.1 with
    | none =>
      have exactPath := (routePathWithSearchWork_spec G s t).1
      rw [produced,selected] at exactPath
      have unreachable : ¬ Reach H s t := by
        intro reachable
        have original : Reach G s t := reach_mono (filter_subset _ _) reachable
        obtain ⟨path,found⟩ := routePath_succeeds.mpr original
        rw [← exactPath] at found
        contradiction
      simpa [grow,R,n] using growFromWithSuccessorTests_unreachableFee H ∅ (empty_subset _) s t unreachable
    | some path =>
      exact growFromWithSuccessorTests_successFee H ∅ R t n s path selected


private theorem routeArcsListWithWordWork_nodup (G : List (V × V)) (t : V) (simple : G.Nodup) :
    (routeArcsListWithWordWork G t (Fintype.card V)).1.Nodup := by
  let n := Fintype.card V
  let annotate (e : V × V) := (e,decide (hops G.toFinset e.2 t < hops G.toFinset e.1 t))
  obtain ⟨same,_⟩ := mapListWithChecks_spec (routeEdgeWithWordWork G t n) annotate G
    (2*hopsListWordBudget n G.length+7)
    (fun e _ => (routeEdgeWithWordWork_spec G t e).1)
    (fun e _ => (routeEdgeWithWordWork_spec G t e).2)
  change (((mapListWithChecks (routeEdgeWithWordWork G t n) G).1.filter Prod.snd).map Prod.fst).Nodup
  rw [same,List.filter_map,List.map_map]
  change ((G.filter (Prod.snd ∘ annotate)).map id).Nodup
  simpa using simple.filter (Prod.snd ∘ annotate)

/-- Recover the prior route fees using the retained hop graph and its shared
reverse-reach list. The supplied input arcs are already unique. -/
def routePathListWithLegacyFees (arcs : List (V × V)) (s t : V) (depth : ℕ) :
    (Option (List (V × V)) × ℕ × ℕ) × ℕ :=
  let H := routeArcsListWithWordWork arcs t depth
  let path := forwardPathWithReachListWork H.1 [] s t depth
  let m := arcs.length
  let kept := H.1.length
  let reached := path.1.2.length
  let length := (path.1.1.map List.length).getD 1
  let visits := ((depth+1)*depth/2)*m
  ((path.1.1,m*(2*visits)+depth*kept,length*(2*reached)),
    H.2+path.2+m+kept+reached+length+36)

theorem routePathListWithLegacyFees_spec (arcs : List (V × V)) (s t : V) (simple : arcs.Nodup) :
    let n := Fintype.card V
    let out := routePathListWithLegacyFees arcs s t n
    out.1 = routePathWithSearchWork arcs.toFinset s t ∧
      out.2 ≤ routePathListWordBudget n arcs.length+2*arcs.length+2*n+36 := by
  let n := Fintype.card V
  let H := routeArcsListWithWordWork arcs t n
  let r := forwardPathWithReachListWork H.1 [] s t n
  let old := routePathWithSearchWork arcs.toFinset s t
  obtain ⟨set,keptCap,filterWork⟩ := routeArcsListWithWordWork_spec arcs t
  have keptSimple := routeArcsListWithWordWork_nodup arcs t simple
  obtain ⟨prior,reachable⟩ := forwardPathWithReachListWork_spec H.1 [] s t
  obtain ⟨path,word,pathLen⟩ := forwardPathListWithWordWork_spec H.1 [] s t
  change (r.1.1,r.2) = forwardPathListWithWordWork H.1 [] s t n at prior
  rw [← prior] at path word pathLen
  have same : r.1.1 = old.1 := by
    rw [show old.1 = routePath arcs.toFinset s t from (routePathWithSearchWork_spec arcs.toFinset s t).1]
    rw [show r.1.1 = _ from path,set]
    rfl
  have originalCount : arcs.length = arcs.toFinset.card := (List.toFinset_card_of_nodup simple).symm
  have keptCount : H.1.length = H.1.toFinset.card := (List.toFinset_card_of_nodup keptSimple).symm
  have reachCount := reachable
  change r.1.2.length = (reaches H.1.toFinset t).card at reachCount
  rw [set] at reachCount
  have triangular : (∑ k ∈ range (n+1), k) = (n+1)*n/2 := by
    rw [sum_range_id,Nat.add_sub_cancel]
  obtain ⟨scan,tests⟩ := routePathWithSearchWork_fees arcs.toFinset s t
  refine ⟨?_,?_⟩
  · change (r.1.1,arcs.length*(2*(((n+1)*n/2)*arcs.length))+n*H.1.length,
      (r.1.1.map List.length).getD 1*(2*r.1.2.length)) = old
    rw [same,originalCount,keptCount,set,reachCount,← triangular]
    exact Prod.ext rfl (Prod.ext scan.symm tests.symm)
  · have reachCap : r.1.2.length ≤ n := reachable.trans_le (card_le_univ _)
    have pathCap : (r.1.1.map List.length).getD 1 ≤ n := by
      change (r.1.1.getD []).length ≤ n at pathLen
      cases selected : r.1.1 with
      | none =>
        have positive : 0 < n := Fintype.card_pos_iff.mpr ⟨s⟩
        simpa [selected] using Nat.succ_le_of_lt positive
      | some path => simpa [selected] using pathLen
    have pathWork : r.2 ≤ reachInListWordBudget n arcs.length+(n+1)*(17+n*(2*arcs.length+20))+4 := by
      simp only [List.length_nil,Nat.add_zero] at word
      refine word.trans ?_
      unfold reachInListWordBudget
      gcongr
    have arcCap : H.1.length ≤ arcs.length := keptCap
    change H.2+r.2+arcs.length+H.1.length+r.1.2.length+(r.1.1.map List.length).getD 1+36 ≤
      routePathListWordBudget n arcs.length+2*arcs.length+2*n+36
    change H.2 ≤ routeArcsListWordBudget n arcs.length at filterWork
    unfold routePathListWordBudget
    omega

/-- Compute the source side from the stored residual rows. -/
def sourceSideFromResidualListWithWordWork (arcs : List (V × V)) (s : V) (depth : ℕ) :
    Finset V × ℕ :=
  let rows := arcs.map Prod.swap
  let reached := reachInListWithWordWork rows s depth
  let set : Finset V := ⟨(reached.1 : Multiset V), by simpa using (reachInListWithWordWork_spec rows s depth).1⟩
  (set,reached.2+7*arcs.length+6)

theorem sourceSideFromResidualListWithWordWork_spec (arcs : List (V × V)) (s : V) :
    let n := Fintype.card V
    let out := sourceSideFromResidualListWithWordWork arcs s n
    out.1 = reaches (reverseArcs arcs.toFinset) s ∧
      out.2 ≤ reachInListWordBudget n arcs.length+7*arcs.length+6 := by
  let n := Fintype.card V
  let rows := arcs.map Prod.swap
  let reached := reachInListWithWordWork rows s n
  obtain ⟨unique,same,work⟩ := reachInListWithWordWork_spec rows s n
  have listed : (⟨(reached.1 : Multiset V),by simpa using unique⟩ : Finset V) = reached.1.toFinset := by
    ext v
    exact List.mem_toFinset.symm
  have reversed : rows.toFinset = reverseArcs arcs.toFinset := by
    ext e
    simp [rows,reverseArcs,List.mem_toFinset,mem_image]
  refine ⟨?_,?_⟩
  · change (⟨(reached.1 : Multiset V),_⟩ : Finset V) = _
    rw [listed,same,reversed]
    rfl
  · change reached.2+7*arcs.length+6 ≤ _
    change reached.2 ≤ reachInListWordBudget n rows.length at work
    rw [show rows.length = arcs.length by simp [rows]] at work
    exact Nat.add_le_add_right (Nat.add_le_add_right work _) _

end OnlineReachabilityPreservers
