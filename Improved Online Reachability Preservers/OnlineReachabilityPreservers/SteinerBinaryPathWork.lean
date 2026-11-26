import OnlineReachabilityPreservers.SteinerBinaryReachWork

/-! Find a shortest simple route on encoded arcs, using the supplied arc order at ties. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def layerWorkBudget (n arcs labels depth : ℕ) : ℕ :=
  2+depth*(5+arcs*(14+2*((5*labels+8)*n)))

private def layerTestWorkBudget (n arcs labels depth : ℕ) : ℕ :=
  layerWorkBudget n arcs labels depth+(5*labels+8)*n+5

private def firstBinaryReachDepthWithWork (arcs : List (List Bool × List Bool)) (source target : List Bool) :
    ℕ → ℕ → Option ℕ × ℕ
  | 0, _ => (none,2)
  | fuel+1, depth =>
    let tested := binaryReachTestListWithWork arcs source target depth
    if tested.1 then (some depth,tested.2+4) else
      let tail := firstBinaryReachDepthWithWork arcs source target fuel (depth+1)
      (tail.1,tested.2+tail.2+5)

private def firstDepthInRange (arcs : Arcs V) (source target : V) (start fuel : ℕ) : Option ℕ → Prop
  | none => ∀ depth, start ≤ depth → depth < start+fuel → source ∉ reachIn arcs target depth
  | some depth => start ≤ depth ∧ depth < start+fuel ∧ source ∈ reachIn arcs target depth ∧
    ∀ earlier, start ≤ earlier → earlier < depth → source ∉ reachIn arcs target earlier

private theorem firstBinaryReachDepthWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (arcs : List (V × V)) (source target : V)
    (maxDepth fuel start : ℕ) (fits : start+fuel ≤ maxDepth+1) :
    let out := firstBinaryReachDepthWithWork (binaryEncodeArcs code arcs) (code source) (code target) fuel start
    firstDepthInRange arcs.toFinset source target start fuel out.1 ∧
      out.2 ≤ 2+fuel*(layerTestWorkBudget (Fintype.card V) arcs.length w maxDepth+5) := by
  let test := fun depth => binaryReachTestListWithWork (binaryEncodeArcs code arcs) (code source) (code target) depth
  let bound := layerTestWorkBudget (Fintype.card V) arcs.length w maxDepth
  induction fuel generalizing start with
  | zero =>
    refine ⟨fun depth low high => ?_,by simp [firstBinaryReachDepthWithWork]⟩
    omega
  | succ fuel ih =>
    obtain ⟨same,work⟩ := binaryReachTestListWithWork_spec code injective w bounded arcs source target start
    obtain ⟨reference,_⟩ := reachTestListWithWordWork_spec arcs source target start
    change (test start).1 = _ at same
    rw [reference] at same
    have testCost : (test start).2 ≤ bound := by
      apply work.trans
      have smaller : start ≤ maxDepth := by omega
      dsimp [bound,layerTestWorkBudget,layerWorkBudget]
      gcongr
    let tail := firstBinaryReachDepthWithWork (binaryEncodeArcs code arcs) (code source) (code target) fuel (start+1)
    let out := if (test start).1 then (some start,(test start).2+4)
      else (tail.1,(test start).2+tail.2+5)
    change firstDepthInRange arcs.toFinset source target start (fuel+1) out.1 ∧ out.2 ≤ 2+(fuel+1)*(bound+5)
    unfold out
    rw [same,Nat.succ_mul fuel]
    by_cases present : source ∈ reachIn arcs.toFinset target start
    · rw [decide_eq_true present]
      refine ⟨⟨le_rfl,by omega,present,?_⟩,?_⟩
      · intro earlier low high
        omega
      · change (test start).2+4 ≤ 2+(fuel*(bound+5)+(bound+5))
        omega
    · rw [decide_eq_false present]
      obtain ⟨value,tailCost⟩ := ih (start+1) (by omega)
      change tail.2 ≤ 2+fuel*(bound+5) at tailCost
      refine ⟨?_,?_⟩
      · change firstDepthInRange arcs.toFinset source target start (fuel+1) tail.1
        change firstDepthInRange arcs.toFinset source target (start+1) fuel tail.1 at value
        cases found : tail.1 with
        | none =>
          rw [found] at value
          intro d low high
          by_cases equal : d = start
          · exact equal.symm ▸ present
          · exact value d (by omega) (by omega)
        | some d =>
          rw [found] at value
          obtain ⟨low,high,reached,minimal⟩ := value
          refine ⟨by omega,by omega,reached,fun earlier first before => ?_⟩
          by_cases equal : earlier = start
          · exact equal.symm ▸ present
          · exact minimal earlier (by omega) before
      · change (test start).2+tail.2+5 ≤ 2+(fuel*(bound+5)+(bound+5))
        omega

private def firstBinaryStepWithWork (source : List Bool) (side : List (List Bool)) :
    List (List Bool × List Bool) → Option (List Bool × List Bool) × ℕ
  | [] => (none,2)
  | arc::rest =>
    let matchesSource := binaryEqualWithWork source arc.1
    let reachesTarget := binaryKeyMemWithWork arc.2 side
    if matchesSource.1 && reachesTarget.1 then (some arc,matchesSource.2+reachesTarget.2+5) else
      let tail := firstBinaryStepWithWork source side rest
      (tail.1,matchesSource.2+reachesTarget.2+tail.2+6)

private def firstBinaryStepWorkBudget (n arcs w : ℕ) : ℕ :=
  2+arcs*(5*w+10+(5*w+8)*n)

private theorem firstBinaryStepWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (source : V) (side : List V) (simple : side.Nodup)
    (arcs : List (V × V)) :
    let out := firstBinaryStepWithWork (code source) (side.map code) (binaryEncodeArcs code arcs)
    let accepted := fun e : V × V => decide (source = e.1 ∧ e.2 ∈ side)
    out.1 = (arcs.find? accepted).map (fun e => (code e.1,code e.2)) ∧
      out.2 ≤ firstBinaryStepWorkBudget (Fintype.card V) arcs.length w := by
  let unit := 5*w+10+(5*w+8)*Fintype.card V
  let accepted := fun e : V × V => decide (source = e.1 ∧ e.2 ∈ side)
  have small : side.length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup simple]
    exact card_le_univ _
  have sourceWidth := bounded source
  induction arcs with
  | nil => simp [firstBinaryStepWithWork,binaryEncodeArcs,firstBinaryStepWorkBudget]
  | cons arc rest ih =>
    let u := binaryEqualWithWork (code source) (code arc.1)
    let v := binaryKeyMemWithWork (code arc.2) (side.map code)
    let tail := firstBinaryStepWithWork (code source) (side.map code) (binaryEncodeArcs code rest)
    let encoded := (code arc.1,code arc.2)
    obtain ⟨uValue,uCost⟩ := binaryEqualWithWork_spec (code source) (code arc.1)
    obtain ⟨vValue,vCost⟩ := binaryKeyMemWithWork_encoded_spec code injective w bounded arc.2 side
    obtain ⟨tailValue,tailCost⟩ := ih
    have passes : (u.1 && v.1) = accepted arc := by
      change u.1 = _ at uValue
      change v.1 = _ at vValue
      rw [uValue,vValue]
      simp only [injective.eq_iff]
      by_cases first : source = arc.1 <;> simp [accepted,first]
    have targetCost : v.2 ≤ 1+(5*w+8)*Fintype.card V :=
      vCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ small) _)
    change u.2 ≤ 5*(code source).length+3 at uCost
    change tail.1 = _ at tailValue
    change tail.2 ≤ 2+rest.length*unit at tailCost
    change (if u.1 && v.1 then (some encoded,u.2+v.2+5) else (tail.1,u.2+v.2+tail.2+6)).1 =
        ((arc::rest).find? accepted).map (fun e => (code e.1,code e.2)) ∧
      (if u.1 && v.1 then (some encoded,u.2+v.2+5) else (tail.1,u.2+v.2+tail.2+6)).2 ≤
        2+(rest.length+1)*unit
    rw [passes,List.find?_cons,Nat.succ_mul rest.length]
    dsimp only [unit] at tailCost ⊢
    cases accepted arc with
    | true =>
      refine ⟨rfl,?_⟩
      change u.2+v.2+5 ≤ _
      omega
    | false =>
      refine ⟨tailValue,?_⟩
      change u.2+v.2+tail.2+6 ≤ _
      omega

private def growBinaryShortestPathWithWork (arcs : List (List Bool × List Bool)) (target : List Bool) :
    ℕ → List Bool → Option (List (List Bool × List Bool)) × ℕ
  | 0, source =>
    let same := binaryEqualWithWork source target
    (if same.1 then some [] else none,same.2+4)
  | depth+1, source =>
    let layer := binaryReachInListWithWork arcs target depth
    let step := firstBinaryStepWithWork source layer.1 arcs
    match step.1 with
    | none => (none,layer.2+step.2+4)
    | some arc =>
      let tail := growBinaryShortestPathWithWork arcs target depth arc.2
      (tail.1.map (arc::·),layer.2+step.2+tail.2+7)

private def growBinaryShortestPathWorkBudget (n arcs w limit steps : ℕ) : ℕ :=
  5*w+7+steps*(layerWorkBudget n arcs w limit+firstBinaryStepWorkBudget n arcs w+7)

omit [Fintype V] in
private theorem walk_vertices_mem_layer {G : Arcs V} {s t : V} {path : List (V × V)}
    (walk : Walk G s t path) : ∀ v ∈ path.map Prod.fst ++ [t], v ∈ reachIn G t path.length := by
  induction walk with
  | nil => simp [reachIn]
  | @cons a b t rest edge walk ih =>
    intro v member
    rcases List.mem_cons.mp member with rfl | tail
    · have next : b ∈ rest.map Prod.fst ++ [t] := by
        cases walk <;> simp
      exact reachIn_succ.mpr (Or.inr ⟨b,edge,ih b next⟩)
    · exact reachIn_subset_succ G t _ (ih v tail)

private theorem growBinaryShortestPathWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (arcs : List (V × V)) (source target : V)
    (limit depth : ℕ) (fits : depth ≤ limit) (present : source ∈ reachIn arcs.toFinset target depth)
    (minimal : ∀ earlier < depth, source ∉ reachIn arcs.toFinset target earlier) :
    let out := growBinaryShortestPathWithWork (binaryEncodeArcs code arcs) (code target) depth (code source)
    (∃ path, out.1 = some (binaryEncodeArcs code path) ∧ SimpleWalk arcs.toFinset source target path ∧
      path.length = depth) ∧ out.2 ≤ growBinaryShortestPathWorkBudget (Fintype.card V) arcs.length w limit depth := by
  induction depth generalizing source with
  | zero =>
    have same : source = target := by simpa [reachIn] using present
    subst source
    let equal := binaryEqualWithWork (code target) (code target)
    obtain ⟨flag,work⟩ := binaryEqualWithWork_spec (code target) (code target)
    have yes : equal.1 = true := by simpa using flag
    have size := bounded target
    change equal.2 ≤ 5*(code target).length+3 at work
    change (∃ p, (if equal.1 then some [] else none) = some (binaryEncodeArcs code p) ∧
      SimpleWalk arcs.toFinset target target p ∧ p.length = 0) ∧
      equal.2+4 ≤ growBinaryShortestPathWorkBudget (Fintype.card V) arcs.length w limit 0
    rw [yes]
    refine ⟨⟨[],rfl,⟨.nil _,by simp⟩,rfl⟩,?_⟩
    unfold growBinaryShortestPathWorkBudget
    omega
  | succ depth ih =>
    let labels := reachInListWithWordWork arcs target depth
    let layer := binaryReachInListWithWork (binaryEncodeArcs code arcs) (code target) depth
    let step := firstBinaryStepWithWork (code source) layer.1 (binaryEncodeArcs code arcs)
    let accepted := fun e : V × V => decide (source = e.1 ∧ e.2 ∈ labels.1)
    obtain ⟨simple,vertices,_⟩ := reachInListWithWordWork_spec arcs target depth
    obtain ⟨layerValue,layerCost⟩ := binaryReachInListWithWork_spec code injective w bounded arcs target depth
    change labels.1.toFinset = _ at vertices
    change layer.1 = labels.1.map code at layerValue
    have steps (e : V × V) : accepted e = true ↔ source = e.1 ∧ e.2 ∈ reachIn arcs.toFinset target depth := by
      rw [← vertices]
      simp [accepted]
    have existsStep : ∃ e ∈ arcs, accepted e = true := by
      rcases reachIn_succ.mp present with before | ⟨next,edge,seen⟩
      · exact (minimal depth (by omega) before).elim
      · exact ⟨(source,next),List.mem_toFinset.mp edge,(steps _).mpr ⟨rfl,seen⟩⟩
    cases pick : arcs.find? accepted with
    | none =>
      obtain ⟨arc,member,yes⟩ := existsStep
      exact ((List.find?_eq_none.mp pick arc member) yes).elim
    | some arc =>
      obtain ⟨rfl,reachesNext⟩ := (steps arc).mp (List.find?_some pick)
      have edge : Edge arcs.toFinset arc.1 arc.2 := List.mem_toFinset.mpr (List.mem_of_find?_eq_some pick)
      have nextMinimum (earlier : ℕ) (small : earlier < depth) (seen : arc.2 ∈ reachIn arcs.toFinset target earlier) : False :=
        minimal (earlier+1) (by omega) (reachIn_succ.mpr (Or.inr ⟨arc.2,edge,seen⟩))
      obtain ⟨⟨rest,tailValue,walk,length⟩,tailCost⟩ := ih arc.2 (by omega) reachesNext nextMinimum
      obtain ⟨stepValue,stepCost⟩ := firstBinaryStepWithWork_spec code injective w bounded arc.1 labels.1 simple arcs
      have first : (firstBinaryStepWithWork (code arc.1) layer.1 (binaryEncodeArcs code arcs)).1 =
          some (code arc.1,code arc.2) := by
        rw [layerValue,show (firstBinaryStepWithWork (code arc.1) (labels.1.map code) (binaryEncodeArcs code arcs)).1 =
          (arcs.find? accepted).map (fun e => (code e.1,code e.2)) from stepValue,pick]
        rfl
      have exactStepCost : (firstBinaryStepWithWork (code arc.1) layer.1 (binaryEncodeArcs code arcs)).2 ≤
          firstBinaryStepWorkBudget (Fintype.card V) arcs.length w := by
        rw [layerValue]
        exact stepCost
      have exactLayerCost : layer.2 ≤ layerWorkBudget (Fintype.card V) arcs.length w limit := by
        apply layerCost.trans
        have smaller : depth ≤ limit := by omega
        unfold layerWorkBudget
        gcongr
      let tail := growBinaryShortestPathWithWork (binaryEncodeArcs code arcs) (code target) depth (code arc.2)
      change tail.1 = _ at tailValue
      change tail.2 ≤ _ at tailCost
      have fresh : arc.1 ∉ rest.map Prod.fst ++ [target] := by
        intro onPath
        have later := walk_vertices_mem_layer walk.1 arc.1 onPath
        rw [length] at later
        exact minimal depth (by omega) later
      rw [growBinaryShortestPathWithWork]
      change (∃ route, (match (firstBinaryStepWithWork (code arc.1) layer.1 (binaryEncodeArcs code arcs)).1 with
        | none => (none,layer.2+(firstBinaryStepWithWork (code arc.1) layer.1 (binaryEncodeArcs code arcs)).2+4)
        | some e =>
          let next := growBinaryShortestPathWithWork (binaryEncodeArcs code arcs) (code target) depth e.2
          (next.1.map (e::·),layer.2+(firstBinaryStepWithWork (code arc.1) layer.1 (binaryEncodeArcs code arcs)).2+next.2+7)).1 =
        some (binaryEncodeArcs code route) ∧ SimpleWalk arcs.toFinset arc.1 target route ∧ route.length = depth+1) ∧ _
      rw [first]
      refine ⟨⟨arc::rest,?_,⟨.cons edge walk.1,?_⟩,by simp [length]⟩,?_⟩
      · change tail.1.map _ = _
        rw [tailValue]
        rfl
      · exact List.nodup_cons.mpr ⟨fresh,walk.2⟩
      · change layer.2+(firstBinaryStepWithWork (code arc.1) layer.1 _).2+tail.2+7 ≤
          growBinaryShortestPathWorkBudget (Fintype.card V) arcs.length w limit (depth+1)
        unfold growBinaryShortestPathWorkBudget at tailCost ⊢
        rw [Nat.succ_mul depth]
        omega

/-- Find the first reachable depth and reconstruct a shortest path using
the order of the supplied encoded arcs. The search depth is a supplied control. -/
def binaryShortestPathWithWork (arcs : List (List Bool × List Bool)) (source target : List Bool)
    (depth : ℕ) : Option (List (List Bool × List Bool)) × ℕ :=
  let earliest := firstBinaryReachDepthWithWork arcs source target (depth+1) 0
  match earliest.1 with
  | none => (none,earliest.2+4)
  | some steps =>
    let path := growBinaryShortestPathWithWork arcs target steps source
    (path.1,earliest.2+path.2+6)

def binaryShortestPathWorkBudget (n arcs w depth : ℕ) : ℕ :=
  2+(depth+1)*(layerTestWorkBudget n arcs w depth+5)+growBinaryShortestPathWorkBudget n arcs w depth depth+6

theorem binaryShortestPathWorkBudget_mono_arcs (n w depth : ℕ) :
    Monotone (fun arcs => binaryShortestPathWorkBudget n arcs w depth) := by
  intro arcs larger within
  change binaryShortestPathWorkBudget n arcs w depth ≤ binaryShortestPathWorkBudget n larger w depth
  unfold binaryShortestPathWorkBudget layerTestWorkBudget growBinaryShortestPathWorkBudget
    layerWorkBudget firstBinaryStepWorkBudget
  gcongr

/-- Success returns a simple path of minimum length at most the supplied depth.
Failure means the target remains unreachable at that depth. -/
theorem binaryShortestPathWithWork_spec (code : V → List Bool) (injective : Function.Injective code)
    (w : ℕ) (bounded : ∀ v, (code v).length ≤ w) (arcs : List (V × V)) (source target : V) (depth : ℕ) :
    let out := binaryShortestPathWithWork (binaryEncodeArcs code arcs) (code source) (code target) depth
    (out.1 = none ∧ source ∉ reachIn arcs.toFinset target depth ∨
      ∃ path, out.1 = some (binaryEncodeArcs code path) ∧ SimpleWalk arcs.toFinset source target path ∧
        path.length ≤ depth ∧ ∀ earlier < path.length, source ∉ reachIn arcs.toFinset target earlier) ∧
      out.2 ≤ binaryShortestPathWorkBudget (Fintype.card V) arcs.length w depth := by
  let bits := binaryEncodeArcs code arcs
  let earliest := firstBinaryReachDepthWithWork bits (code source) (code target) (depth+1) 0
  obtain ⟨earliestValue,earliestWork⟩ := firstBinaryReachDepthWithWork_spec code injective w bounded arcs source target
    depth (depth+1) 0 (by omega)
  change earliest.2 ≤ _ at earliestWork
  change firstDepthInRange arcs.toFinset source target 0 (depth+1) earliest.1 at earliestValue
  let out := match earliest.1 with
    | none => (none,earliest.2+4)
    | some steps =>
      let path := growBinaryShortestPathWithWork bits (code target) steps (code source)
      (path.1,earliest.2+path.2+6)
  change (out.1 = none ∧ source ∉ reachIn arcs.toFinset target depth ∨
      ∃ path, out.1 = some (binaryEncodeArcs code path) ∧ SimpleWalk arcs.toFinset source target path ∧
        path.length ≤ depth ∧ ∀ earlier < path.length, source ∉ reachIn arcs.toFinset target earlier) ∧ out.2 ≤ _
  unfold out
  cases found : earliest.1 with
  | none =>
    rw [found] at earliestValue
    refine ⟨Or.inl ⟨rfl,earliestValue depth (by omega) (by omega)⟩,?_⟩
    change earliest.2+4 ≤ binaryShortestPathWorkBudget (Fintype.card V) arcs.length w depth
    unfold binaryShortestPathWorkBudget
    omega
  | some steps =>
    rw [found] at earliestValue
    obtain ⟨_,fits,present,minimal⟩ := earliestValue
    obtain ⟨⟨path,value,simple,length⟩,cost⟩ := growBinaryShortestPathWithWork_spec code injective w bounded arcs source target
      depth steps (by omega) present (fun earlier small => minimal earlier (by omega) small)
    refine ⟨Or.inr ⟨path,value,simple,by omega,?_⟩,?_⟩
    · rw [length]
      exact fun earlier small => minimal earlier (by omega) small
    · change earliest.2+(growBinaryShortestPathWithWork bits (code target) steps (code source)).2+6 ≤ _
      unfold binaryShortestPathWorkBudget
      have costFit := cost.trans (show growBinaryShortestPathWorkBudget (Fintype.card V) arcs.length w depth steps ≤
          growBinaryShortestPathWorkBudget (Fintype.card V) arcs.length w depth depth from by
        unfold growBinaryShortestPathWorkBudget
        gcongr
        omega)
      exact Nat.add_le_add_right (Nat.add_le_add earliestWork costFit) _

/-- Enlarge the graph dimensions, encoded label width, and search depth. -/
theorem binaryShortestPathWorkBudget_le {n n' arcs arcs' width width' depth depth' : ℕ}
    (vertices : n ≤ n') (edges : arcs ≤ arcs') (labels : width ≤ width') (steps : depth ≤ depth') :
    binaryShortestPathWorkBudget n arcs width depth ≤ binaryShortestPathWorkBudget n' arcs' width' depth' := by
  unfold binaryShortestPathWorkBudget layerTestWorkBudget growBinaryShortestPathWorkBudget
    layerWorkBudget firstBinaryStepWorkBudget
  gcongr

end OnlineReachabilityPreservers
