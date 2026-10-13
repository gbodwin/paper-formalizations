import DirectedFlowCutGap.AdaptivePackingSelectedData

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def selectionWork {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n)
    (q : BinaryFractionalCore.Choice n) (label : Fin n → Bits) : ℕ :=
  BinaryIndexedPairRead.steps (label q.bottleneck)+17+
    (NormalizedRow.steps s.weights.toList q.mask.toList+8+
    (ObjectiveRow.steps capacity.toList (normalized s.weights q.mask).1.toList+13+
    (RationalComparisonProgram.instructions s.bestCost (objective capacity (normalized s.weights q.mask).1).1+2+
      selectionSteps (BinaryRational.le s.bestCost (objective capacity (normalized s.weights q.mask).1).1).1)))

theorem active_selection {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap original input d : ℕ}
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ steps ext, ∃ out : NaturalState 4800,
      ∃ data : SelectedData out.heap out.registers.c cap original input label capacity s
        (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1,
      NaturalRun program steps (state heap next cap original input d stack source 4402) [] out ∧
      out.heap=heap++ext ∧ out.next=next+ext.length ∧ out.stack=stack ∧ out.source=source ∧ out.pc=4472 ∧
      out.registers.a=data.best ∧ out.registers.b=data.cost ∧
      (∀ W,1≤W → (∀ i,(label i).length≤W) →
        (∀ x∈s.weights.toList,StoredBounded x W) → (∀ i,StoredBounded (get capacity i) W) →
        steps ≤ GraphOracleMachine.instructionBound ds.length n W+29+
          selectionWork capacity s (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1 label) := by
  let q := (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn s.weights).1
  let w := (normalized s.weights q.mask).1
  let candidate := (objective capacity w).1
  let keep := (BinaryRational.le s.bestCost candidate).1
  obtain ⟨o⟩ := original_data stateRep
  obtain ⟨demands,metadata,inputCell,demandRep,metadataRep⟩ := inputRep
  obtain ⟨t₁,e₁,choice,f₁,r₁,cf₁,choiceRep,prefixBound⟩ := actual_choice_prefix adjacency capacity s.weights label numeric hn
    encoded (a:=cap) (d:=d) o.first inputCell o.weightsRep metadataRep demandRep next dense stack source
  let n₁ := next+e₁.length
  let o₁ := o.extend e₁
  obtain ⟨e₂,mask,amount,l₂,r₂,af,amountRep,maskRep⟩ := actual_amount_handover (d:=choice) capacity q label numeric cf₁
    o₁.first choiceRep (list_extend capRep e₁) n₁ (by simp [n₁,List.length_append,dense]) stack source
  let n₂ := n₁+e₂.length
  let f₂ := n₁+q.bottleneck.val+2
  let o₂ := o₁.extend e₂
  obtain ⟨e₃,normalized,l₃,r₃,nf,normalizedRep⟩ := actual_normalized_handover (d:=amount) af
    o₂.weightsRep maskRep (by simp) n₂ (by simp [n₂,n₁,List.length_append,dense,Nat.add_assoc]) stack source
  rw [NormalizedRow.result_eq_normalized] at normalizedRep
  let n₃ := n₂+e₃.length
  let f₃ := n₂+NormalizedRow.cells s.weights.toList q.mask.toList
  let o₃ := o₂.extend e₃
  have caps₃ := list_extend (list_extend (list_extend capRep e₁) e₂) e₃
  obtain ⟨e₄,candidateRoot,l₄,r₄,cf, candidateRep⟩ := actual_objective_handover (d:=normalized) nf o₃.costPath
    caps₃ normalizedRep (by simp) n₃ (by simp [n₃,n₂,n₁,List.length_append,dense,Nat.add_assoc]) stack source
  rw [ObjectiveRow.result_eq_objective] at candidateRep
  let n₄ := n₃+e₄.length
  let f₄ := n₃+ObjectiveRow.cells capacity.toList w.toList
  let o₄ := o₃.extend e₄
  obtain ⟨e₅,flag,_,r₅⟩ := actual_best_handover (d:=candidateRoot) s.bestCost candidate cf o₄.bestPath o₄.costPath
    o₄.costRep candidateRep n₄ (by simp [n₄,n₃,n₂,n₁,List.length_append,dense,Nat.add_assoc]) stack source
  let h := heap++e₁++e₂++e₃++e₄++e₅
  let o₅ := o₄.extend e₅
  have nrep : StoredList h normalized w.toList := list_extend (list_extend normalizedRep e₄) e₅
  have crep : Stored h candidateRoot candidate := stored_extend candidateRep e₅
  have brep : StoredList h (if keep then o.best else normalized) (if keep then s.best else w).toList := by
    cases keep
    · exact nrep
    · exact o₅.bestRep
  have costrep : Stored h (if keep then o.cost else candidateRoot) (if keep then s.bestCost else candidate) := by
    cases keep
    · exact crep
    · exact o₅.costRep
  let data : SelectedData h f₄ cap original input label capacity s q :=
    ⟨choice,amount,normalized,candidateRoot,(if keep then o.best else normalized),(if keep then o.cost else candidateRoot),
      o₅,(by simpa [h,List.append_assoc] using list_extend caps₃ (e₄++e₅)),candidate_frame_extend cf e₅,
      (by simpa [h,List.append_assoc] using choice_extend choiceRep (e₂++e₃++e₄++e₅)),
      (by simpa [h,List.append_assoc] using stored_extend amountRep (e₃++e₄++e₅)),
      nrep,crep,brep,costrep⟩
  let out := state h (n₄+e₅.length) data.best data.cost f₄ flag stack source 4472
  refine ⟨t₁ + ((BinaryIndexedPairRead.steps (label q.bottleneck)+17) +
    ((NormalizedRow.steps s.weights.toList q.mask.toList+8) +
    ((ObjectiveRow.steps capacity.toList w.toList+13) +
    (RationalComparisonProgram.instructions s.bestCost candidate+2+selectionSteps keep)))),
    e₁++e₂++e₃++e₄++e₅,out,data,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
  · exact run_append r₁ (run_append r₂ (run_append r₃ (run_append r₄ r₅)))
  · simp [out,h,state,List.append_assoc]
  · simp [out,state,n₄,n₃,n₂,n₁,List.length_append,Nat.add_assoc]
  · intro W hW labels weights capacities
    have hb := prefixBound W hW labels weights capacities
    change t₁+selectionWork capacity s q label ≤ _
    exact Nat.add_le_add_right hb _
end DirectedFlowCutGap.AdaptivePackingState
