import OnlineReachabilityPreservers.BackwardCopyReturns
import OnlineReachabilityPreservers.IncidenceGirthCleaning

/-! A short bridge can be created by splitting the common label of two
incidence cycles, even when only one cycle is shorter than the cutoff. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset SimpleGraph
open scoped Sigma.Lex

private def mixedCycleSource : Fin 10 → Fin 20 := ![4,0,3,3,2,3,3,3,0,1]
private def mixedCycleTarget : Fin 10 → Fin 20 := ![3,3,5,6,3,4,7,8,1,2]

/-- A three-step detour and its river, with a directed two-cycle at the
terminal and four outgoing edges to private leaves. -/
def mixedCycleRows (i : Fin 10) : List (Fin 20) := [mixedCycleSource i,mixedCycleTarget i]

private theorem mixed_before :
    ∀ (i : Fin 10) (x y : Fin 20), BeforeIn mixedCycleRows i x y ↔
      x = mixedCycleSource i ∧ y = mixedCycleTarget i := by
  unfold BeforeIn
  decide

private def mixedPrefix (r : Fin 10) : Arcs (Fin 20) :=
  ((univ.erase r).filter fun i => mixedCycleSource i ≠ mixedCycleTarget r).image
    fun i => (mixedCycleSource i,mixedCycleTarget i)

set_option maxRecDepth 10000 in
private theorem mixed_no_earlier_final :
    ∀ (r a : Fin 10), a < r → mixedCycleTarget a = mixedCycleTarget r →
      mixedCycleSource r ∉ reaches (mixedPrefix r) (mixedCycleSource a) := by
  decide

/-- None of the original bridges has its last arc earlier than its river,
at any cutoff. -/
theorem mixedCycleRows_halfFree (k : ℕ) : HalfBridgeFree (BeforeIn mixedCycleRows) k := by
  intro d _ b earlier
  let r := b.river
  let a := b.arc (Fin.last d)
  let v := b.vertex ∘ Fin.castSucc (n := d+1)
  obtain ⟨source,target⟩ := (mixed_before _ _ _).mp b.riverStep
  have terminal : BeforeIn mixedCycleRows a (v (Fin.last d)) (b.vertex (Fin.last (d+1))) := by
    simpa only [v,a,Function.comp_apply,Fin.succ_last] using b.arcStep (Fin.last d)
  obtain ⟨before,finish⟩ := (mixed_before _ _ _).mp terminal
  have step (i : Fin d) : Edge (mixedPrefix r) (v i.castSucc) (v i.succ) := by
    let j := b.arc i.castSucc
    have mark : BeforeIn mixedCycleRows j (v i.castSucc) (v i.succ) := by
      simpa only [v,j,Function.comp_apply,Fin.succ_castSucc] using b.arcStep i.castSucc
    obtain ⟨left,right⟩ := (mixed_before _ _ _).mp mark
    refine mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_erase.mpr ⟨(b.river_ne_arc _).symm,mem_univ _⟩,?_⟩,
      Prod.ext left.symm right.symm⟩
    intro finishes
    have same : b.vertex ((i.castSucc : Fin (d+1)).castSucc) = b.vertex (Fin.last (d+1)) :=
      left.trans (finishes.trans target.symm)
    have ident := congrArg Fin.val (b.distinctVertices same)
    simp only [Fin.val_castSucc,Fin.val_last] at ident
    have bound := i.isLt
    omega
  have reaches := mem_reaches.mpr (reachIn_sound (reachIn_of_fin_steps v step))
  apply mixed_no_earlier_final r a earlier (finish.symm.trans target)
  have start : v 0 = mixedCycleSource r := source
  rwa [← start,← before]

theorem mixedCycleRows_original_widths :
    (∀ i, (mixedCycleRows i).Nodup) ∧
    (let M := ∑ i, (mixedCycleRows i).length
     M = 20 ∧ 4*M/20 = 4 ∧ 4*M/10 = 8) := by decide

private abbrev MixedCopy := ListVertexBlockIndex mixedCycleRows 4
private abbrev MixedPiece := ListBlockIndex (splitListVertices mixedCycleRows 4) 8

set_option synthInstance.maxSize 1024 in
/-- At the exact original width four, the copies of the common terminal
are distinct. The directed two-cycle completes a new earlier-final detour. -/
theorem mixedCycleRows_width_split_creates_half_six :
    ¬ HalfBridgeFree (BeforeIn (listRegularizedPaths mixedCycleRows 4 8)) 6 := by
  let vertex : Fin 6 → MixedCopy :=
    ![⟨0,⟨0,by decide⟩⟩,⟨1,⟨0,by decide⟩⟩,⟨2,⟨0,by decide⟩⟩,⟨3,⟨1,by decide⟩⟩,
      ⟨4,⟨0,by decide⟩⟩,⟨3,⟨0,by decide⟩⟩]
  let arc : Fin 5 → MixedPiece :=
    ![⟨8,⟨0,by decide⟩⟩,⟨9,⟨0,by decide⟩⟩,⟨4,⟨0,by decide⟩⟩,⟨5,⟨0,by decide⟩⟩,⟨0,⟨0,by decide⟩⟩]
  let r : MixedPiece := ⟨1,⟨0,by decide⟩⟩
  have distinctVertices : ∀ i j, vertex i = vertex j → i = j := by decide
  have distinctRows : ∀ i j, arc i = arc j → i = j := by decide
  have rowApart : ∀ i, r.fst ≠ (arc i).fst := by decide
  have riverApart (i) : r ≠ arc i := fun same => rowApart i (congrArg Sigma.fst same)
  have river : BeforeIn (listRegularizedPaths mixedCycleRows 4 8) r (vertex 0) (vertex (Fin.last 5)) := by
    unfold BeforeIn
    decide
  have steps : ∀ i, BeforeIn (listRegularizedPaths mixedCycleRows 4 8) (arc i) (vertex i.castSucc) (vertex i.succ) := by
    unfold BeforeIn
    decide
  have earlier : arc (Fin.last 4) < r := Sigma.Lex.left _ _ (by decide : (0 : Fin 10) < 1)
  intro free
  exact free (k := 4) (by decide)
    ⟨vertex,arc,r,fun {_ _} => distinctVertices _ _,fun {_ _} => distinctRows _ _,riverApart,river,steps⟩
    earlier

private abbrev MixedNode := Fin 10 ⊕ Fin 20
private abbrev mixedCycleGraph := pathIncidenceGraph mixedCycleRows

private instance mixedCycleAdjDecidable : DecidableRel mixedCycleGraph.Adj
  | .inl i, .inr v => inferInstanceAs (Decidable (v ∈ mixedCycleRows i))
  | .inr v, .inl i => inferInstanceAs (Decidable (v ∈ mixedCycleRows i))
  | .inl _, .inl _ => isFalse id
  | .inr _, .inr _ => isFalse id

private def shortIncidenceCycle : mixedCycleGraph.Walk (Sum.inr 3) (Sum.inr 3) :=
  Walk.ofSupport [Sum.inr 3,Sum.inl 5,Sum.inr 4,Sum.inl 0,Sum.inr 3] (by decide) (by decide)

private def longIncidenceCycle : mixedCycleGraph.Walk (Sum.inr 3) (Sum.inr 3) :=
  Walk.ofSupport [Sum.inr 3,Sum.inl 1,Sum.inr 0,Sum.inl 8,Sum.inr 1,Sum.inl 9,Sum.inr 2,Sum.inl 4,Sum.inr 3]
    (by decide) (by decide)

private theorem shortIncidenceCycle_isCycle : shortIncidenceCycle.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  refine ⟨by decide,?_,by decide⟩
  intro nil
  have len : shortIncidenceCycle.length = 4 := by decide
  simp only [nil,Walk.length_nil] at len
  omega

private theorem longIncidenceCycle_isCycle : longIncidenceCycle.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  refine ⟨by decide,?_,by decide⟩
  intro nil
  have len : longIncidenceCycle.length = 8 := by decide
  simp only [nil,Walk.length_nil] at len
  omega

/-- The two relevant cycles have lengths four and eight, meeting at the
terminal with disjoint edges. Their total length reaches twice six. -/
theorem mixedCycleRows_noShortCyclePair_fails : ¬ NoShortCyclePair mixedCycleGraph 6 := by
  have checked : Disjoint shortIncidenceCycle.edges.toFinset longIncidenceCycle.edges.toFinset := by decide
  have separate : Disjoint shortIncidenceCycle.edgeSet longIncidenceCycle.edgeSet := by
    rw [Set.disjoint_left]
    intro e left right
    exact Finset.disjoint_left.mp checked (List.mem_toFinset.mpr left) (List.mem_toFinset.mpr right)
  intro claim
  have long := claim _ _ _ shortIncidenceCycle_isCycle longIncidenceCycle_isCycle separate
  have total : shortIncidenceCycle.length + longIncidenceCycle.length = 12 := by decide
  omega

private def shortCycleSharedEdge : Sym2 MixedNode := s(Sum.inr 3,Sum.inl 0)

private def avoidCycleEdge : ℕ → MixedNode → MixedNode → List MixedNode → Bool
  | 0,here,goal,_ => decide (here = goal)
  | d+1,here,goal,available => available.any fun next =>
      decide (mixedCycleGraph.Adj here next ∧ s(here,next) ≠ shortCycleSharedEdge) &&
        avoidCycleEdge d next goal (available.filter fun v => decide (v ≠ next))

private theorem avoidCycleEdge_complete {start goal : MixedNode} (w : mixedCycleGraph.Walk start goal)
    (available : List MixedNode) (avoided : shortCycleSharedEdge ∉ w.edges)
    (distinct : w.support.tail.Nodup) (confined : w.support.tail ⊆ available) :
    avoidCycleEdge w.length start goal available = true := by
  induction w generalizing available with
  | nil => simp [avoidCycleEdge]
  | @cons start next goal edge rest ih =>
    simp only [Walk.support_cons,List.tail_cons] at distinct confined
    have vertices : rest.support = next :: rest.support.tail := by cases rest <;> rfl
    have fresh := List.nodup_cons.mp (vertices ▸ distinct)
    have present : next ∈ available := confined rest.start_mem_support
    have approved : s(start,next) ≠ shortCycleSharedEdge := by
      intro equal
      exact avoided (by simp only [Walk.edges_cons,List.mem_cons,← equal,true_or])
    have notUsed : shortCycleSharedEdge ∉ rest.edges :=
      fun used => avoided (by simp only [Walk.edges_cons,List.mem_cons,used,or_true])
    have remains (vertex : MixedNode) (on : vertex ∈ rest.support.tail) :
        vertex ∈ available.filter (fun v => decide (v ≠ next)) := by
      refine List.mem_filter.mpr ⟨confined (List.mem_of_mem_tail on),decide_eq_true ?_⟩
      intro eq
      exact fresh.1 (eq ▸ on)
    simp only [Walk.length_cons,avoidCycleEdge]
    refine List.any_eq_true.mpr ⟨next,present,?_⟩
    have step : decide (mixedCycleGraph.Adj start next ∧ s(start,next) ≠ shortCycleSharedEdge) = true :=
      decide_eq_true ⟨edge,approved⟩
    rw [step,Bool.true_and]
    exact ih _ notUsed fresh.2 (fun _ h => remains _ h)

private def mixedNodes : List MixedNode :=
  ((List.finRange 10).map Sum.inl) ++ ((List.finRange 20).map Sum.inr)

private theorem mixedNodes_contains (node : MixedNode) : node ∈ mixedNodes := by
  cases node <;> simp [mixedNodes]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem mixedCycle_search_excludes_cycles :
    ∀ (a : MixedNode) (d : Fin 7), 3 ≤ d.val → avoidCycleEdge d.val a a mixedNodes = false := by
  decide

private theorem mixedCycle_short_walks_use_same_edge {a : MixedNode}
    (w : mixedCycleGraph.Walk a a) (cycle : w.IsCycle) (short : w.length ≤ 6) :
    shortCycleSharedEdge ∈ w.edges := by
  by_contra absent
  let d : Fin 7 := ⟨w.length,by omega⟩
  have excluded := mixedCycle_search_excludes_cycles a d cycle.three_le_length
  have found := avoidCycleEdge_complete w mixedNodes absent cycle.support_nodup
    (fun vertex _ => mixedNodes_contains vertex)
  rw [excluded] at found
  contradiction

/-- If both individual lengths are at most six, the two cycles cannot
have disjoint edges. This weaker test still lets the width split fail. -/
theorem mixedCycleRows_no_disjoint_cycles_each_at_most_six :
    ∀ a (x y : mixedCycleGraph.Walk a a), x.IsCycle → y.IsCycle → x.length ≤ 6 → y.length ≤ 6 →
      ¬ Disjoint x.edgeSet y.edgeSet := by
  intro a x y xc yc xl yl separate
  exact Set.disjoint_left.mp separate (mixedCycle_short_walks_use_same_edge x xc xl)
    (mixedCycle_short_walks_use_same_edge y yc yl)

end OnlineReachabilityPreservers.SourceAudit
