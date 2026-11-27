import OnlineReachabilityPreservers.HalfFiveTerminalRank

/-! Realize terminal ranks as copied paths and compare the local and arrival tests. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

namespace SourceAudit

/-- A pair of full three-bridges ends at vertex two, with a two-step
return from the final row to the later river's row. -/
def terminalRankExampleRows : Fin 6 → List (Fin 5) :=
  ![[3,2],[3,1],[0,2],[0,1],[1,2,0],[4,2]]

def terminalRankExampleAssignment (i : Fin 6) (v : Fin 5) : ℕ :=
  if v = 2 ∧ (i = 2 ∨ i = 4) then 1 else 0

local instance terminalRankExampleBefore (i : Fin 6) (x y : Fin 5) :
    Decidable (Before terminalRankExampleRows i x y) := by
  unfold BeforeIn
  infer_instance

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
private theorem terminalExample_no_disagreeing_prefix :
    ∀ (r a : Fin 6) (x y z : Fin 5), a < r → Before terminalRankExampleRows r x z →
      Before terminalRankExampleRows a y z → x ∉ reaches (bridgePrefixGraph terminalRankExampleRows r a) y := by
  decide +kernel

/-- Omitting the river and final arc from a putative earlier-ending
bridge leaves an impossible prefix route. -/
theorem terminalRankExampleRows_halfFree (k : ℕ) : HalfBridgeFree (Before terminalRankExampleRows) k := by
  intro d _ b earlier
  exact (terminalExample_no_disagreeing_prefix b.river (b.arc (Fin.last d)) _ _ _ earlier
    b.riverStep (b.arcStep (Fin.last d))) (mem_reaches.mpr b.reaches_prefix_excluding_river_and_final)

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
private theorem terminalExample_three_increases :
    ∀ (r f a : Fin 6) (x y z : Fin 5), r ≠ f → r ≠ a → f ≠ a →
      Before terminalRankExampleRows r x z → Before terminalRankExampleRows f x y →
      Before terminalRankExampleRows a y z → terminalRankExampleAssignment r z ≤ terminalRankExampleAssignment a z := by
  decide +kernel

private theorem terminalExample_return_increases :
    ∀ (r a : Fin 6) (x y : Fin 5), Before terminalRankExampleRows r x y →
      Before terminalRankExampleRows a y x → terminalRankExampleAssignment r x ≤ terminalRankExampleAssignment a x := by
  decide +kernel

/-- The local rank graph accepts the assigned ranks at every vertex. -/
theorem terminalRankExampleAssignment_increases (v : Fin 5) {r a : Fin 6}
    (step : Edge (halfFiveTerminalRankGraph terminalRankExampleRows v) r a) :
    terminalRankExampleAssignment r v ≤ terminalRankExampleAssignment a v := by
  rcases halfFiveTerminalRankGraph_edge.mp step with ⟨b,rfl,rfl,rfl⟩ | ⟨y,first,last⟩
  · exact terminalExample_three_increases _ _ _ _ _ _ (b.river_ne_arc 0) (b.river_ne_arc 1)
      (fun eq => (by decide : (0 : Fin 2) ≠ 1) (b.distinctArcs eq))
      b.riverStep (b.arcStep 0) (b.arcStep 1)
  · exact terminalExample_return_increases r a v y first last

/-- A three-bridge edge and a return edge force the two ranks at
vertex two to agree in every assignment respecting the terminal graph. -/
theorem terminalRankExample_two_rows_sameComponent :
    SameComponent (halfFiveTerminalRankGraph terminalRankExampleRows 2) 2 4 := by
  let b : Bridge (Before terminalRankExampleRows) 1 := threeListBridge
    (a := 3) (b := 4) (r := 2) (x := 0) (y := 1) (z := 2)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have forward : Edge (halfFiveTerminalRankGraph terminalRankExampleRows 2) 2 4 :=
    halfFiveTerminalRankGraph_edge.mpr (Or.inl ⟨b,rfl,rfl,rfl⟩)
  have reverse : Edge (halfFiveTerminalRankGraph terminalRankExampleRows 2) 4 2 :=
    halfFiveTerminalRankGraph_edge.mpr (Or.inr ⟨0,by decide +kernel,by decide +kernel⟩)
  exact ⟨.single forward,.single reverse⟩

/-- The explicit degree copies preserve half-five exclusion. -/
theorem terminalRankExampleCopies_halfFree :
    HalfBridgeFree (Before (halfFiveRankedVertexCopies terminalRankExampleRows terminalRankExampleAssignment)) 5 := by
  exact halfFiveRankedVertexCopies_halfFree (by decide +kernel) (terminalRankExampleRows_halfFree 5)
    terminalRankExampleAssignment (fun v {_ _} => terminalRankExampleAssignment_increases v)

/-- Two rows ending in the same original vertex have ranks decreasing
with their arrival order. The local test permits this split. -/
theorem terminalRankExample_nonmonotone_terminals :
    ∃ i j : Fin 6, i < j ∧ ∃ x y v : Fin 5,
      Before terminalRankExampleRows i x v ∧ Before terminalRankExampleRows j y v ∧
      terminalRankExampleAssignment j v < terminalRankExampleAssignment i v := by
  exact ⟨4,5,by decide,1,4,2,by decide +kernel,by decide +kernel,by decide⟩

end SourceAudit
end OnlineReachabilityPreservers
