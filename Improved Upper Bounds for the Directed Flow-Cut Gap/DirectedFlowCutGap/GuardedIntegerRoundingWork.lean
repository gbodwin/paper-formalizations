import DirectedFlowCutGap.PaidGuardedExecution
import DirectedFlowCutGap.PhysicalIntegerRounding
import DirectedFlowCutGap.OriginalGraphCostEnvelope

/-! The hard packed-rounding branch keeps its incurred work when its
literal tape ends. The original output and successful charges are unchanged. -/
namespace DirectedFlowCutGap.GuardedIntegerRoundingWork

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open PhysicalIntegerRounding (Result boundaryWords fromWord maskCopyCharge)
open RawGraphInputStore (prepare)
open RawGraphControllerProgram (program instructionBound)
open OriginalGraphCostEnvelope (preparedCells preparedCells_eq)
open PhysicalCoverAccess (Read)
open CachedReferenceExecution (FastState)

def readMask (s : FastState 26704) : Read Bits :=
  PhysicalCoverAccess.readWordWith (CachedReferenceHeap.read s.store) s.store.cells.size s.registers.d

theorem readMask_eq (s : FastState 26704) :
    readMask s=PhysicalCoverAccess.readWord s.freeze.heap s.freeze.registers.d := by
  have h : CachedReferenceHeap.read s.store=PhysicalCoverAccess.access s.store.cells.toList :=
    funext (CachedReferenceHeap.read_eq s.store)
  simp only [readMask,h,PhysicalCoverAccess.readWord,CachedReferenceExecution.FastState.freeze,Array.length_toList]

private theorem readList_length {A : Type} (get : Bits → Read (Cell Bits)) (item : Bits → Read A)
    (fuel : ℕ) (root : Bits) {xs : List A}
    (done : (PhysicalCoverAccess.readListWith get item fuel root).1=some xs) : xs.length ≤ fuel := by
  induction fuel generalizing root xs with
  | zero => cases done
  | succ fuel ih =>
      rw [PhysicalCoverAccess.readListWith,Read.bind_value] at done
      cases cell : (get root).1 with
      | none => simp [cell] at done
      | some c =>
          cases c with
          | nil =>
              simp [cell] at done
              subst xs
              exact Nat.zero_le _
          | flag _ => simp [cell] at done
          | pair head tail =>
              simp only [cell,Option.bind_some,Read.bind_value] at done
              cases read : (item head).1 with
              | none => simp [read] at done
              | some x =>
                  cases body : (PhysicalCoverAccess.readListWith get item fuel tail).1 with
                  | none => simp [read,body] at done
                  | some ys =>
                      simp only [read,body,Option.bind_some,Read.pure_value,Option.some.injEq] at done
                      rw [← done,List.length_cons]
                      exact Nat.succ_le_succ (ih tail body)

private theorem readMask_length (s : FastState 26704) {bits : Bits} (done : (readMask s).1=some bits) :
    bits.length ≤ s.store.cells.size := by
  unfold readMask PhysicalCoverAccess.readWordWith at done
  exact readList_length _ _ _ _ done

def collect {n : ℕ} (prepared boundary control : ℕ)
    (execution : Option (FastState 26704) × ℕ) : Read (Result n) :=
  let work := prepared+execution.2
  match execution.1 with
  | none => (none,work+boundary+control)
  | some final =>
      let restored := readMask final
      let base := work+restored.2+boundary
      match restored.1 with
      | none => (none,base+control)
      | some bits =>
          let paid := base+maskCopyCharge n bits.length
          (some ⟨fromWord n bits,final.source,paid⟩,paid+control)

private theorem collect_value {n : ℕ} (prepared boundary control : ℕ)
    (execution : Option (FastState 26704) × ℕ) :
    (collect (n:=n) prepared boundary control execution).1 = (do
      let (out, paid) ← execution.1.map (fun s => (s.freeze,execution.2))
      let observed := PhysicalCoverAccess.readWord out.heap out.registers.d
      let mask ← observed.1
      pure ⟨fromWord n mask,out.source,prepared+paid+observed.2+boundary+maskCopyCharge n mask.length⟩) := by
  unfold collect
  cases reached : execution.1 with
  | none => rfl
  | some final =>
      simp only [Option.map_some,readMask_eq,FastState.freeze]
      let observed := PhysicalCoverAccess.readWord final.store.cells.toList final.registers.d
      let decode (mask : Bits) : Result n :=
        ⟨fromWord n mask,final.source,prepared+execution.2+observed.2+boundary+maskCopyCharge n mask.length⟩
      change (match observed.1 with
        | none => (none,prepared+execution.2+observed.2+boundary+control)
        | some mask => (some (decode mask),(decode mask).paid+control)).1=
        observed.1.bind (fun mask => some (decode mask))
      cases observed.1 <;> rfl

theorem collect_paid_le {n : ℕ} (prepared boundary control : ℕ)
    (execution : Option (FastState 26704) × ℕ) (readBudget cells : ℕ)
    (read : ∀ s, execution.1=some s → (readMask s).2 ≤ readBudget ∧ s.store.cells.size ≤ cells) :
    (collect (n:=n) prepared boundary control execution).2 ≤
      prepared+execution.2+boundary+readBudget+maskCopyCharge n cells+control := by
  unfold collect
  cases run : execution.1 with
  | none =>
      change prepared+execution.2+boundary+control ≤ _
      omega
  | some final =>
      obtain ⟨pay,size⟩ := read final run
      dsimp only
      cases mask : (readMask final).1 with
      | none =>
          change prepared+execution.2+(readMask final).2+boundary+control ≤ _
          omega
      | some bits =>
          have length := (readMask_length final mask).trans size
          have copy : maskCopyCharge n bits.length ≤ maskCopyCharge n cells := by
            unfold maskCopyCharge
            gcongr
          change prepared+execution.2+(readMask final).2+boundary+maskCopyCharge n bits.length+control ≤ _
          omega

def runPacked (n : ℕ) (entry : BitState 26704 × ℕ) (boundary fuel : ℕ) : Read (Result n) :=
  let encoded := BinaryNaturalView.encode fuel
  let executed := PaidGuardedExecution.executeBinary program encoded.1 (FastState.ofReference entry.1) 0
  collect entry.2 boundary (encoded.2+executed.2) executed.1

def hard {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) : Read (Result n) :=
  let words := boundaryWords n L T
  let matrix := GraphRelaxationRefinement.matrix adj
  let entry := prepare matrix words.dimension words.level words.trials tape
  runPacked n entry words.paid (instructionBound n L (preparedCells n L T+1) T.bits+1)

private theorem execute_reference {C : ℕ} (p : Program C) (fuel : ℕ)
    (entry : BitState C) :
    let encoded := BinaryNaturalView.encode fuel
    let done := (PaidGuardedExecution.executeBinary p encoded.1 (FastState.ofReference entry) 0).1
    done.1.map (fun s => (s.freeze,done.2))=GuardedReferenceExecution.execute p fuel entry 0 := by
  dsimp only
  rw [(PaidGuardedExecution.binary_spec ..).1, BinaryNaturalView.encode_bits, value_bits]
  rw [← CachedGuardedReferenceExecution.execute_ofReference,← PaidGuardedExecution.observation]
  simp only [Option.map_map,Function.comp_def]

attribute [local irreducible] RawGraphControllerProgram.instructionBound RawGraphControllerProgram.program
  RawGraphInputStore.prepare RawGraphInputStore.cells BinaryNaturalView.encode
  GuardedReferenceExecution.execute

theorem hard_value {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) :
    (hard T adj L tape).1=PhysicalIntegerRounding.hardRun T adj L tape := by
  simp only [hard,runPacked,collect_value,execute_reference,PhysicalIntegerRounding.hardRun_reference,
    PhysicalIntegerRounding.boundary_dimension,PhysicalIntegerRounding.boundary_level,
    PhysicalIntegerRounding.boundary_trials,preparedCells_eq]

end DirectedFlowCutGap.GuardedIntegerRoundingWork
