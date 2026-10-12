import DirectedFlowCutGap.CostedCandidateSelection

/-! Uniform stored-input bounds for the actual collection/selection run.
No cost-width or per-candidate computed cost is supplied by the caller. -/
namespace DirectedFlowCutGap.CostedCandidateBounds
open BinaryArithmetic BinaryRational CostedCandidateMaterialization

def InputBound (B M : ℕ) (x : Candidate) : Prop :=
  x.words.length ≤ M ∧ x.sourceWord.length ≤ B ∧ ∀ w∈x.words,w.length ≤ B

def instructionBound (k M B N : ℕ) : ℕ :=
  k*(MaterializedPathSum.instructionBound M B N B+21)+
    (6400*(M*(B+1)+2)^2+12)*k+10

theorem path_bound (rows : List Fraction) (x : Candidate) (M B N : ℕ)
    (hB : 1 ≤ B) (rowWidths : ∀ q∈rows,StoredBounded q B) (bound : InputBound B M x)
    (valid : ∀ w∈x.words,value w<rows.length) (indices : ∀ w∈x.words,value w ≤ N) :
    MaterializedPathSum.steps rows x.sourceWord x.words+1 ≤
      MaterializedPathSum.instructionBound M B N B := by
  have h := MaterializedPathSum.steps_bound rows x.sourceWord x.words B N hB rowWidths bound.2.2 valid indices
  refine h.trans ?_
  unfold MaterializedPathSum.instructionBound CanonicalRationalSum.instructionBound
  gcongr <;> first | exact bound.1 | exact bound.2.1

theorem score_width (rows : List Fraction) (x : Candidate) (M B : ℕ)
    (hB : 1 ≤ B) (rowWidths : ∀ q∈rows,StoredBounded q B) (bound : InputBound B M x)
    (valid : ∀ w∈x.words,value w<rows.length) : StoredBounded (score rows x) (M*(B+1)+1) := by
  have widths := PathCostMaterialization.costs_width rows x.sourceWord x.words B hB rowWidths valid
  have hs := BinaryFractionalRows.sum_stored_bound (PathCostMaterialization.costs rows x.sourceWord x.words) B
    (fun q hq => BinaryFractionalRows.stored_raw_bound (widths q hq))
  have len : (PathCostMaterialization.costs rows x.sourceWord x.words).length=x.words.length := by simp [PathCostMaterialization.costs]
  rw [len] at hs
  have hm : x.words.length*(B+1)+1 ≤ M*(B+1)+1 := by gcongr;exact bound.1
  exact ⟨hs.1.trans hm,hs.2.trans hm⟩

theorem item_widths (rows : List Fraction) (xs : List Candidate) (next M B : ℕ)
    (hB : 1 ≤ B) (rowWidths : ∀ q∈rows,StoredBounded q B)
    (bound : ∀ x∈xs,InputBound B M x) (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length) :
    ∀ q∈items rows next xs,RetainedArgminProgram.Fits (M*(B+1)+1) q := by
  induction xs with
  | nil => simp [items]
  | cons x xs ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact score_width rows x M B hB rowWidths (bound x (by simp)) (valid x (by simp))
    · exact ih (fun y hy => bound y (by simp [hy])) (fun y hy => valid y (by simp [hy])) q hq

theorem items_length (rows : List Fraction) (next : ℕ) (xs : List Candidate) :
    (items rows next xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [items] using ih

theorem collection_bound (rows : List Fraction) (xs : List Candidate) (M B N : ℕ)
    (hB : 1 ≤ B) (rowWidths : ∀ q∈rows,StoredBounded q B)
    (bound : ∀ x∈xs,InputBound B M x) (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length)
    (indices : ∀ x∈xs,∀ w∈x.words,value w ≤ N) :
    CostedCandidateMaterialization.steps rows xs ≤
      xs.length*(MaterializedPathSum.instructionBound M B N B+21)+3 := by
  induction xs with
  | nil => simp [CostedCandidateMaterialization.steps]
  | cons x xs ih =>
    have hc := path_bound rows x M B N hB rowWidths (bound x (by simp))
      (valid x (by simp)) (indices x (by simp))
    have ht := ih (fun y hy => bound y (by simp [hy])) (fun y hy => valid y (by simp [hy]))
      (fun y hy => indices y (by simp [hy]))
    simp only [CostedCandidateMaterialization.steps,List.length_cons]
    nlinarith

theorem steps_bound (rows : List Fraction) (xs : List Candidate) (next M B N : ℕ)
    (hB : 1 ≤ B) (rowWidths : ∀ q∈rows,StoredBounded q B)
    (bound : ∀ x∈xs,InputBound B M x) (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length)
    (indices : ∀ x∈xs,∀ w∈x.words,value w ≤ N) :
    CostedCandidateSelection.steps rows next xs ≤ instructionBound xs.length M B N := by
  have hm := collection_bound rows xs M B N hB rowWidths bound valid indices
  have hs := RetainedArgminProgram.steps_bound (items rows next xs)
    (item_widths rows xs next M B hB rowWidths bound valid)
  rw [items_length] at hs
  change RetainedArgminProgram.steps (items rows next xs) ≤
    (6400*(M*(B+1)+2)^2+12)*xs.length+5 at hs
  simp only [CostedCandidateSelection.steps,instructionBound]
  omega

open ImmutableReferenceSimulation ImmutableReferenceTerminal

/-- Uniform polynomial trace budget derived from original stored input sizes. -/
theorem select_bit_bounded {xs : List Candidate} {rows : List Fraction} {H A : ℕ}
    (initial : BitState 501) (bounded : initial.Bounded H A) (pc0 : initial.pc=305)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : CandidateList (eraseState initial).heap (eraseState initial).registers.a xs)
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b
      (IndexedRationalRead.fields rows))
    (M B N : ℕ) (hB : 1 ≤ B) (rowWidths : ∀ q∈rows,StoredBounded q B)
    (bound : ∀ x∈xs,InputBound B M x) (valid : ∀ x∈xs,∀ w∈x.words,value w<rows.length)
    (indices : ∀ x∈xs,∀ w∈x.words,value w ≤ N) :
    ∃ charge out, Run CostedCandidateSelection.program
        (CostedCandidateSelection.steps rows (value initial.next) xs) charge initial [] out ∧
      RetainedArgminProgram.Selected (eraseState out).heap (eraseState out).registers.d
        (RetainedArgminProgram.select (items rows (value initial.next) xs)) ∧
      CandidateList (eraseState out).heap (eraseState initial).registers.a xs ∧
      (∃ itemRoot,RetainedArgminProgram.ItemList (eraseState out).heap itemRoot (items rows (value initial.next) xs)) ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=CostedCandidateSelection.cells rows (value initial.next) xs) ∧
      (attempt CostedCandidateSelection.program out).result=none ∧
      charge+(attempt CostedCandidateSelection.program out).operations ≤
        completeBound 501 H A (instructionBound xs.length M B N) := by
  obtain ⟨charge,out,run,sel,retained,itemRep,src,stack,ext,halt,cost⟩ :=
    CostedCandidateSelection.select_bit initial bounded pc0 hn empty input table valid
  have hs := steps_bound rows xs (value initial.next) M B N hB rowWidths bound valid indices
  have hc : completeBound 501 H A (CostedCandidateSelection.steps rows (value initial.next) xs) ≤
      completeBound 501 H A (instructionBound xs.length M B N) := by
    unfold completeBound runBound stepBound
    gcongr
  exact ⟨charge,out,run,sel,retained,itemRep,src,stack,ext,halt,cost.trans hc⟩

end DirectedFlowCutGap.CostedCandidateBounds
