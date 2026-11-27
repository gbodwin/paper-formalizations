import OnlineReachabilityPreservers.HalfFiveTerminalRank

/-! The terminal-rank test can force both copies of a reversed pair to meet. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped Prod.Lex

/-- Two rows reverse their common pair. Two more rows close a
return cycle at each of the shared vertices. -/
def terminalCoincidenceRows : Fin 4 → List (Fin 6) :=
  ![[5,0,1,2],[3,1,0,4],[2,1,3],[4,0,5]]

local instance terminalCoincidenceBefore (i : Fin 4) (x y : Fin 6) :
    Decidable (BeforeIn terminalCoincidenceRows i x y) := by
  unfold BeforeIn
  infer_instance

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
private theorem coincidence_no_prefix :
    ∀ (r a : Fin 4) (x y z : Fin 6), r ≠ a → BeforeIn terminalCoincidenceRows r x z →
      BeforeIn terminalCoincidenceRows a y z → x ∉ reaches (bridgePrefixGraph terminalCoincidenceRows r a) y := by
  decide +kernel

/-- The original family excludes full bridges at every size. -/
theorem terminalCoincidenceRows_fullFree (k : ℕ) : BridgeFree (BeforeIn terminalCoincidenceRows) k := by
  intro d _
  refine ⟨fun b => ?_⟩
  exact (coincidence_no_prefix b.river (b.arc (Fin.last d)) _ _ _ (b.river_ne_arc _)
    b.riverStep (b.arcStep (Fin.last d))) (mem_reaches.mpr b.reaches_prefix_excluding_river_and_final)

private theorem terminalCoincidence_return (r a : Fin 4) (v w : Fin 6)
    (first : BeforeIn terminalCoincidenceRows r v w) (last : BeforeIn terminalCoincidenceRows a w v) :
    Edge (halfFiveTerminalRankGraph terminalCoincidenceRows v) r a :=
  halfFiveTerminalRankGraph_edge.mpr (Or.inr ⟨w,first,last⟩)

/-- The two reversed rows lie in the same terminal component at both
endpoints, with each equality forced by an explicit return cycle. -/
theorem terminalCoincidenceRows_components :
    SameComponent (halfFiveTerminalRankGraph terminalCoincidenceRows 0) 0 1 ∧
    SameComponent (halfFiveTerminalRankGraph terminalCoincidenceRows 1) 0 1 := by
  have atZero01 := terminalCoincidence_return 0 1 0 1 (by decide +kernel) (by decide +kernel)
  have atZero13 := terminalCoincidence_return 1 3 0 4 (by decide +kernel) (by decide +kernel)
  have atZero30 := terminalCoincidence_return 3 0 0 5 (by decide +kernel) (by decide +kernel)
  have atOne10 := terminalCoincidence_return 1 0 1 0 (by decide +kernel) (by decide +kernel)
  have atOne02 := terminalCoincidence_return 0 2 1 2 (by decide +kernel) (by decide +kernel)
  have atOne21 := terminalCoincidence_return 2 1 1 3 (by decide +kernel) (by decide +kernel)
  exact ⟨⟨.single atZero01,.tail (.single atZero13) atZero30⟩,
    ⟨.tail (.single atOne02) atOne21,.single atOne10⟩⟩

/-- Every assignment respecting the terminal graph leaves two distinct
copies shared by the first two rows of this example. -/
theorem terminalCoincidenceRankedCopies_share_two
    (assigned : Fin 4 → Fin 6 → ℕ)
    (increases : ∀ v ⦃r a⦄, Edge (halfFiveTerminalRankGraph terminalCoincidenceRows v) r a →
      assigned r v ≤ assigned a v) :
    ∃ x y : Fin 6 ×ₗ ℕ, x ≠ y ∧
      x ∈ halfFiveRankedVertexCopies terminalCoincidenceRows assigned 0 ∧
      x ∈ halfFiveRankedVertexCopies terminalCoincidenceRows assigned 1 ∧
      y ∈ halfFiveRankedVertexCopies terminalCoincidenceRows assigned 0 ∧
      y ∈ halfFiveRankedVertexCopies terminalCoincidenceRows assigned 1 := by
  have zero : assigned 0 0 = assigned 1 0 :=
    halfFiveTerminalRank_eq_of_sameComponent (fun {_ _} e => increases 0 e) terminalCoincidenceRows_components.1
  have one : assigned 0 1 = assigned 1 1 :=
    halfFiveTerminalRank_eq_of_sameComponent (fun {_ _} e => increases 1 e) terminalCoincidenceRows_components.2
  let x : Fin 6 ×ₗ ℕ := toLex (0,assigned 0 0)
  let y : Fin 6 ×ₗ ℕ := toLex (1,assigned 0 1)
  have apart : x ≠ y := fun eq => (by decide : (0 : Fin 6) ≠ 1) (congrArg (fun a => (ofLex a).1) eq)
  refine ⟨x,y,apart,List.mem_map.mpr ⟨0,by decide +kernel,rfl⟩,?_,
    List.mem_map.mpr ⟨1,by decide +kernel,rfl⟩,?_⟩
  · exact List.mem_map.mpr ⟨0,by decide +kernel,by simp only [x,zero]⟩
  · exact List.mem_map.mpr ⟨1,by decide +kernel,by simp only [y,one]⟩

end OnlineReachabilityPreservers.SourceAudit
