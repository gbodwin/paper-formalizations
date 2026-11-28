import OnlineReachabilityPreservers.SteinerDistanceHopRounds
import OnlineReachabilityPreservers.SteinerUnaryRoundPriorArchiveMachine

/-! Encode a simultaneous distance-column relaxation as rectangular transfers. -/

namespace OnlineReachabilityPreservers

open StateTransition Turing

/-- A diagonal transfer costs zero, an off-diagonal arc costs one,
and a missing transfer takes the remaining code. -/
def steinerHopTransferCode {n : ℕ} (G : Arcs (Fin n)) (pair : Fin n × Fin n) : ℕ :=
  if pair.1 = pair.2 then 0 else if Edge G pair.1 pair.2 then 1 else 2

/-- Missing transfers produce the sentinel for the row minimum. -/
def steinerHopTransferCandidate (n code previous : ℕ) : ℕ :=
  if code ≤ 1 then previous+code else n+1

/-- Pair every source's transfer codes with the same previous column. -/
def steinerHopTransferRound {n : ℕ} (codes : Fin n × Fin n → ℕ) (previous : Vector ℕ n) : Vector ℕ n :=
  Vector.ofFn fun source => (List.ofFn fun next : Fin n =>
    steinerHopTransferCandidate n (codes (source,next)) previous[next.val]).foldl min (n+1)

private theorem hopTransferMin_le (values : List ℕ) {n limit : ℕ} (cap : limit ≤ n) :
    values.foldl min (n+1) ≤ limit ↔ ∃ value ∈ values, value ≤ limit := by
  rw [List.foldl_min,min_le_iff]
  cases found : values.min? with
  | none =>
    have empty := List.min?_eq_none_iff.mp found
    subst values
    simp
    omega
  | some least =>
    have spec := List.min?_eq_some_iff.mp found
    simp only [Option.getD_some]
    constructor
    · rintro (invalid | within)
      · omega
      · exact ⟨least,spec.1,within⟩
    · rintro ⟨value,on,within⟩
      exact Or.inr ((spec.2 value on).trans within)

private theorem hopTransfer_candidates_le {n limit : ℕ} (G : Arcs (Fin n))
    (previous : Fin n × Fin n → ℕ) (source target : Fin n) (cap : limit ≤ n) :
    ((List.ofFn fun next : Fin n =>
      steinerHopTransferCandidate n (steinerHopTransferCode G (source,next)) (previous (next,target))).foldl min (n+1)) ≤ limit ↔
      previous (source,target) ≤ limit ∨ ∃ next, Edge G source next ∧ previous (next,target)+1 ≤ limit := by
  rw [hopTransferMin_le _ cap]
  constructor
  · rintro ⟨value,member,small⟩
    obtain ⟨next,rfl⟩ := List.mem_ofFn.mp member
    by_cases same : source = next
    · subst next
      exact Or.inl (by simpa [steinerHopTransferCode,steinerHopTransferCandidate] using small)
    · by_cases edge : Edge G source next
      · exact Or.inr ⟨next,edge,by simpa [steinerHopTransferCode,steinerHopTransferCandidate,same,edge] using small⟩
      · simp [steinerHopTransferCode,steinerHopTransferCandidate,same,edge] at small
        omega
  · rintro (old | ⟨next,edge,small⟩)
    · refine ⟨previous (source,target),List.mem_ofFn.mpr ⟨source,?_⟩,old⟩
      simp [steinerHopTransferCode,steinerHopTransferCandidate]
    · by_cases same : source = next
      · subst next
        refine ⟨previous (source,target),List.mem_ofFn.mpr ⟨source,?_⟩,by omega⟩
        simp [steinerHopTransferCode,steinerHopTransferCandidate]
      · refine ⟨previous (next,target)+1,List.mem_ofFn.mpr ⟨next,?_⟩,small⟩
        simp [steinerHopTransferCode,steinerHopTransferCandidate,same,edge]

/-- The rectangular code rows give an exact simultaneous distance
column. The common starting cap is the unreachable sentinel. -/
theorem steinerHopTransferRound_eq_hopRounds {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (target : Fin n) :
    steinerHopTransferRound (steinerHopTransferCode G)
      (Vector.ofFn fun source => steinerDistanceHopRounds G depth (source,target)) =
      Vector.ofFn fun source => steinerDistanceHopRounds G (depth+1) (source,target) := by
  ext i hi
  let source : Fin n := ⟨i,hi⟩
  let previous := steinerDistanceHopRounds G depth
  let values := List.ofFn fun next : Fin n =>
    steinerHopTransferCandidate n (steinerHopTransferCode G (source,next)) (previous (next,target))
  let observed := values.foldl min (n+1)
  let expected := steinerDistanceHopRounds G (depth+1) (source,target)
  simp only [steinerHopTransferRound,Vector.getElem_ofFn]
  change observed = expected
  have observedCap : observed ≤ n+1 := by
    dsimp only [observed]
    rw [List.foldl_min]
    exact min_le_left _ _
  have expectedCap : expected ≤ n+1 := by
    simpa only [Fintype.card_fin] using steinerDistanceHopRounds_cap G (depth+1) (source,target)
  have agrees (limit : ℕ) (cap : limit ≤ n) : observed ≤ limit ↔ expected ≤ limit := by
    have fit : limit ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using cap
    exact (hopTransfer_candidates_le G previous source target cap).trans
      (steinerDistanceHopStep_le G previous source target fit).symm
  apply le_antisymm
  · by_cases small : expected ≤ n
    · exact (agrees expected small).mpr le_rfl
    · omega
  · by_cases small : observed ≤ n
    · exact (agrees observed small).mp le_rfl
    · omega

/-- Stage the same transfer code rows in the existing rectangular
frame, with the previous hop column stored exactly once. -/
def steinerHopTransferRoundRequest {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (target : Fin n) :
    SteinerUnaryDistanceRoundRequest where
  cap := n+1
  columns := n
  prior := Vector.ofFn fun source => steinerDistanceHopRounds G depth (source,target)
  distances := List.ofFn fun source => Vector.ofFn fun next => steinerHopTransferCode G (source,next)

/-- The existing native frame adapter pairs each encoded transfer with
its previous value in source-row and successor-column order. -/
theorem steinerHopTransferRoundRequest_pairs {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (target : Fin n) :
    steinerUnaryDistanceRoundPairs (steinerHopTransferRoundRequest G depth target) =
      (n+1,List.ofFn fun source => List.ofFn fun next =>
        (steinerHopTransferCode G (source,next),steinerDistanceHopRounds G depth (next,target))) := by
  unfold steinerUnaryDistanceRoundPairs
  apply congrArg (Prod.mk (n+1))
  change (((List.ofFn fun source : Fin n => Vector.ofFn fun next : Fin n => steinerHopTransferCode G (source,next)).map
      Vector.toList).map (fun row => row.zip
        (Vector.ofFn fun next : Fin n => steinerDistanceHopRounds G depth (next,target)).toList)) = _
  simp only [List.map_ofFn,Function.comp_def,Vector.toList_ofFn]
  apply congrArg (@List.ofFn (List (ℕ × ℕ)) n)
  funext source
  apply List.ext_getElem
  · simp [List.length_zip]
  · intro i _ _
    simp only [List.getElem_zip,List.getElem_ofFn]

/-- The prior stores n values at most n+1, and each code costs at most
two unary tallies. The compact frame has quadratic length. -/
theorem encodeSteinerHopTransferRoundRequest_length_le {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (target : Fin n) :
    (encodeSteinerUnaryDistanceRound (steinerHopTransferRoundRequest G depth target)).length ≤ 4*n^2+4*n+3 := by
  let request := steinerHopTransferRoundRequest G depth target
  let rows := request.distances.map Vector.toList
  have prior : (encodeSteinerUnaryRoundPriorVector request.prior.toList).length ≤ n*(n+2) := by
    apply encodeSteinerUnaryRoundPriorVector_length_le
    intro i
    change (Vector.ofFn fun source => steinerDistanceHopRounds G depth (source,target))[i.val] ≤ n+1
    simpa only [Vector.getElem_ofFn,Fintype.card_fin] using
      steinerDistanceHopRounds_cap G depth (⟨i.val,i.isLt⟩,target)
  have each (source : Fin n) :
      (encodeSteinerUnaryRoundPriorVector (List.ofFn fun next => steinerHopTransferCode G (source,next))).length ≤ n*3 := by
    have fits : ∀ next : Fin n, (Vector.ofFn fun j => steinerHopTransferCode G (source,j))[next.val] ≤ 2 := by
      intro next
      simp only [Vector.getElem_ofFn,steinerHopTransferCode]
      split_ifs <;> decide
    simpa only [Vector.toList_ofFn] using encodeSteinerUnaryRoundPriorVector_length_le _ fits
  have matrix : (encodeSteinerUnaryRoundDistances rows).length ≤ n*(n*3+1) := by
    simp only [rows,request,steinerHopTransferRoundRequest,List.map_ofFn,Function.comp_def,Vector.toList_ofFn,
      encodeSteinerUnaryRoundDistances,List.length_flatMap,List.length_append,List.length_singleton,List.sum_ofFn]
    calc
      _ ≤ ∑ _ : Fin n, (n*3+1) := Finset.sum_le_sum fun source _ => Nat.add_le_add_right (each source) 1
      _ = _ := by simp
  have cap : (encodeSteinerUnaryRoundCap request.cap).length = n+2 := by
    simp [request,steinerHopTransferRoundRequest,encodeSteinerUnaryRoundCap]
  change (encodeSteinerUnaryDistanceRound request).length ≤ _
  rw [encodeSteinerUnaryDistanceRound_components]
  simp only [List.length_append,List.length_cons,cap]
  dsimp only [rows] at matrix
  calc
    _ ≤ n+2+n*(n+2)+(n*(n*3+1)+1) := by omega
    _ = _ := by ring

/-- On the supplied previous column, the native adapter prepares the
exact ordered code-and-value cells of the relaxation. -/
def steinerUnaryDistanceRoundFrameMachine_hopTransfer {n : ℕ} (G : Arcs (Fin n)) (depth : ℕ) (target : Fin n) :
    let request := steinerHopTransferRoundRequest G depth target
    let X := (encodeSteinerUnaryDistanceRound request).length
    TM2OutputsInTime steinerUnaryDistanceRoundFrameMachine (encodeSteinerUnaryDistanceRound request)
      (some (encodeSteinerUnarySharedCapRows (n+1,List.ofFn fun source => List.ofFn fun next =>
        (steinerHopTransferCode G (source,next),steinerDistanceHopRounds G depth (next,target))))) (4*X^2+7*X+5) := by
  simpa only [steinerUnaryDistanceRoundFrameAnswer,steinerHopTransferRoundRequest_pairs] using
    steinerUnaryDistanceRoundFrameMachine_run (steinerHopTransferRoundRequest G depth target)

end OnlineReachabilityPreservers
