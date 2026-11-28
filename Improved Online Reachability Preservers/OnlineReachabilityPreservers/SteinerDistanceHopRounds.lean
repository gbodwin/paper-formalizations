import OnlineReachabilityPreservers.SteinerDistanceTable

/-! Compute all hop distances by simultaneous unit-cost relaxations. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- One array entry for every potential successor. Missing arcs use
the same sentinel as the exact hop distance. -/
def steinerDistanceHopCandidates (G : Arcs V) (previous : V × V → ℕ) (source target : V) : List ℕ :=
  ((univ : Finset V).sort (· ≤ ·)).map fun next =>
    if Edge G source next then previous (next,target)+1 else Fintype.card V+1

theorem steinerDistanceHopCandidates_length (G : Arcs V) (previous : V × V → ℕ) (source target : V) :
    (steinerDistanceHopCandidates G previous source target).length = Fintype.card V := by
  simp [steinerDistanceHopCandidates]

/-- Retain the old entry and relax every outgoing arc at unit cost. -/
def steinerDistanceHopStep (G : Arcs V) (previous : V × V → ℕ) (d : V × V) : ℕ :=
  (steinerDistanceHopCandidates G previous d.1 d.2).foldl min (previous d)

/-- Start with zero for the diagonal and a sentinel everywhere else.
One round uses a single previous table for all entries. -/
def steinerDistanceHopRounds (G : Arcs V) : ℕ → V × V → ℕ
  | 0,d => if d.1 = d.2 then 0 else Fintype.card V+1
  | height+1,d => steinerDistanceHopStep G (steinerDistanceHopRounds G height) d

private theorem foldHopMinimum_le (candidates : List ℕ) (old limit : ℕ) :
    candidates.foldl min old ≤ limit ↔ old ≤ limit ∨ ∃ value ∈ candidates, value ≤ limit := by
  induction candidates generalizing old with
  | nil => simp
  | cons value tail ih =>
    rw [List.foldl_cons,ih,min_le_iff]
    constructor
    · rintro ((oldSmall|first)|⟨k,on,small⟩)
      · exact Or.inl oldSmall
      · exact Or.inr ⟨value,List.mem_cons_self ..,first⟩
      · exact Or.inr ⟨k,List.mem_cons_of_mem _ on,small⟩
    · rintro (oldSmall|⟨k,on,small⟩)
      · exact Or.inl (Or.inl oldSmall)
      · rcases List.mem_cons.mp on with same | later
        · subst k
          exact Or.inl (Or.inr small)
        · exact Or.inr ⟨k,later,small⟩

/-- A step reaches a threshold by retaining its entry or by prepending
one actual graph arc to a previous value below that threshold. -/
theorem steinerDistanceHopStep_le (G : Arcs V) (previous : V × V → ℕ) (source target : V)
    {limit : ℕ} (cap : limit ≤ Fintype.card V) :
    steinerDistanceHopStep G previous (source,target) ≤ limit ↔
      previous (source,target) ≤ limit ∨ ∃ next, Edge G source next ∧ previous (next,target)+1 ≤ limit := by
  rw [steinerDistanceHopStep,foldHopMinimum_le]
  unfold steinerDistanceHopCandidates
  constructor
  · rintro (old|⟨value,member,small⟩)
    · exact Or.inl old
    · obtain ⟨next,_on,rfl⟩ := List.mem_map.mp member
      split_ifs at small with edge
      · exact Or.inr ⟨next,edge,small⟩
      · omega
  · rintro (old|⟨next,edge,small⟩)
    · exact Or.inl old
    · exact Or.inr ⟨previous (next,target)+1,
        List.mem_map.mpr ⟨next,by simp,by simp [edge]⟩,small⟩

/-- A table entry is within a threshold exactly when reverse search
reaches its source within both that threshold and the round budget. -/
theorem steinerDistanceHopRounds_le (G : Arcs V) (depth : ℕ) (source target : V)
    {limit : ℕ} (cap : limit ≤ Fintype.card V) :
    steinerDistanceHopRounds G depth (source,target) ≤ limit ↔ source ∈ reachIn G target (min depth limit) := by
  induction depth generalizing source target limit with
  | zero =>
    by_cases same : source = target
    · simp [steinerDistanceHopRounds,reachIn,same]
    · simp [steinerDistanceHopRounds,reachIn,same,show ¬ Fintype.card V+1 ≤ limit by omega]
  | succ depth ih =>
    rw [steinerDistanceHopRounds,steinerDistanceHopStep_le G _ _ _ cap]
    cases limit with
    | zero =>
      have prior : steinerDistanceHopRounds G depth (source,target) ≤ 0 ↔ source ∈ reachIn G target 0 := by
        simpa only [Nat.min_zero] using ih source target (limit := 0) (Nat.zero_le _)
      rw [Nat.min_zero,← prior]
      constructor
      · rintro (old|⟨_,_,small⟩)
        · exact old
        · omega
      · exact Or.inl
    | succ limit =>
      have rewriteDepth : min (depth+1) (limit+1) = min depth limit+1 := by omega
      rw [rewriteDepth]
      have search := monotone_nat_of_le_succ (reachIn_subset_succ G target)
      have below : limit ≤ Fintype.card V := by omega
      constructor
      · rintro (old|⟨next,edge,small⟩)
        · exact search (show min depth (limit+1) ≤ min depth limit+1 by omega) ((ih source target cap).mp old)
        · exact reachIn_succ.mpr (Or.inr ⟨next,edge,(ih next target below).mp (by omega)⟩)
      · intro accepted
        rcases reachIn_succ.mp accepted with old | ⟨next,edge,reached⟩
        · exact Or.inl ((ih source target cap).mpr (search (by omega) old))
        · exact Or.inr ⟨next,edge,Nat.succ_le_succ ((ih next target below).mpr reached)⟩

/-- Every stored entry is at most one above the vertex count. -/
theorem steinerDistanceHopRounds_cap (G : Arcs V) (depth : ℕ) (d : V × V) :
    steinerDistanceHopRounds G depth d ≤ Fintype.card V+1 := by
  have fold_le (candidates : List ℕ) (old : ℕ) : candidates.foldl min old ≤ old := by
    induction candidates generalizing old with
    | nil => exact le_rfl
    | cons value tail ih => exact (ih (min old value)).trans (min_le_left _ _)
  induction depth with
  | zero =>
    unfold steinerDistanceHopRounds
    split <;> omega
  | succ depth ih => exact (fold_le _ _).trans ih

/-- The least successful original search depth has the same threshold
interpretation below the unreachable sentinel. -/
theorem steinerHops_le_iff_reachIn (G : Arcs V) (source target : V) {limit : ℕ} (cap : limit ≤ Fintype.card V) :
    hops G source target ≤ limit ↔ source ∈ reachIn G target limit := by
  let candidates := (range (Fintype.card V+1)).filter (fun k => source ∈ reachIn G target k)
  change (least? candidates).getD (Fintype.card V+1) ≤ limit ↔ _
  constructor
  · intro bounded
    cases found : least? candidates with
    | none => simp only [found,Option.getD_none] at bounded; omega
    | some k =>
      simp only [found,Option.getD_some] at bounded
      have on : k ∈ candidates := least?_mem found
      exact monotone_nat_of_le_succ (reachIn_subset_succ G target) bounded (mem_filter.mp on).2
  · intro reached
    have inside : limit ∈ candidates := mem_filter.mpr ⟨mem_range.mpr (by omega),reached⟩
    obtain ⟨k,found⟩ := least?_some ⟨limit,inside⟩
    simp only [found,Option.getD_some]
    exact least?_le found inside

/-- The hop convention returns at most the unreachable sentinel. -/
theorem steinerHops_le_cap (G : Arcs V) (source target : V) : hops G source target ≤ Fintype.card V+1 := by
  let candidates := (range (Fintype.card V+1)).filter (fun k => source ∈ reachIn G target k)
  change (least? candidates).getD (Fintype.card V+1) ≤ Fintype.card V+1
  cases found : least? candidates with
  | none => simp
  | some k =>
    have on : k ∈ candidates := least?_mem found
    exact Nat.le_of_lt (mem_range.mp (mem_filter.mp on).1)

/-- One simultaneous pass per vertex yields the exact hop table,
including zero diagonal entries and the unreachable sentinel. -/
theorem steinerDistanceHopRounds_exact (G : Arcs V) (d : V × V) :
    steinerDistanceHopRounds G (Fintype.card V) d = hops G d.1 d.2 := by
  let n := Fintype.card V
  let candidate := steinerDistanceHopRounds G n d
  let expected := hops G d.1 d.2
  have before : candidate ≤ n+1 := steinerDistanceHopRounds_cap G n d
  have after : expected ≤ n+1 := steinerHops_le_cap G d.1 d.2
  have agrees (k : ℕ) (cap : k ≤ n) : candidate ≤ k ↔ expected ≤ k := by
    rw [steinerHops_le_iff_reachIn G d.1 d.2 cap]
    simpa only [min_eq_right cap] using steinerDistanceHopRounds_le G n d.1 d.2 cap
  change candidate = expected
  apply le_antisymm
  · by_cases small : expected ≤ n
    · exact (agrees expected small).mpr le_rfl
    · omega
  · by_cases small : candidate ≤ n
    · exact (agrees candidate small).mp le_rfl
    · omega

end OnlineReachabilityPreservers
