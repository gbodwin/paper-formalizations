import DirectedFlowCutGap.CandidatePortGapProgram

/-!
# Select the shift word for a threshold implication

The inputs include the two sign cells, the same-port and reverse-adjacency
flags, and the stored grid and gap words. The program selects an existing
word or allocates the canonical zero word.
-/

namespace DirectedFlowCutGap.CandidateShiftSelectProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Point)

inductive Choice where
  | grid | gap | nilWord
  deriving DecidableEq

def choose (a b same edge : Bool) : Choice :=
  if a then
    if !b && same then .gap else .grid
  else
    if b && (same || edge) then .nilWord else .grid

def word (grid gap : Bits) (a b same edge : Bool) : Bits :=
  match choose a b same edge with
  | .grid => grid
  | .gap => gap
  | .nilWord => []

def relationSteps (a b same : Bool) : ℕ :=
  if a != b then if !a && !same then 4 else 2 else 0

def steps (a b same : Bool) : ℕ := 4+relationSteps a b same+1

theorem steps_le (a b same : Bool) : steps a b same ≤ 9 := by
  cases a <;> cases b <;> cases same <;> decide

theorem word_value {n : ℕ} (D : Input n) (grid bound : Bits) (a b : Point n) :
    value (word grid (CandidatePortGapProgram.gap D grid (BinaryMinimumWordProgram.word grid bound) a.1)
      a.2 b.2 (decide (a.1=b.1)) (CandidatePortAdjacencyProgram.result D b.1 a.1)) =
      CandidateCapacityFlags.shift D (value grid) (value bound) a b := by
  rcases a with ⟨p,s⟩
  rcases b with ⟨q,t⟩
  cases s <;> cases t <;> by_cases eq : p=q <;>
    cases edge : CandidatePortAdjacencyProgram.result D q p <;>
    simp [word,choose,CandidateCapacityFlags.shift,value,CandidatePortGapProgram.gap_value,
      ← CandidatePortAdjacencyProgram.result_eq, *]

def Flags (heap : NaturalHeap) (root : ℕ) (a b : Bool) : Prop :=
  ∃ x y,heap[root]?=some (.pair x y) ∧ heap[x]?=some (.flag a) ∧ heap[y]?=some (.flag b)

def program : Program 24 := fun pc => match pc.val with
  | 0 => .field .r3 .r2 false 1
  | 1 => .branch .r3 23 2 5 23
  | 2 => .field .r3 .r2 true 3
  | 3 => .branch .r3 23 12 8 23
  | 5 => .field .r3 .r2 true 6
  | 6 => .branch .r3 23 10 12 23
  | 8 => .field .r3 .r1 false 9
  | 9 => .branch .r3 23 16 14 23
  | 10 => .field .r3 .r1 false 11
  | 11 => .branch .r3 23 12 13 23
  | 12 => .field .r3 .r0 false 20
  | 13 => .field .r3 .r0 true 20
  | 14 => .make .r3 .nil 20
  | 16 => .field .r3 .r1 true 17
  | 17 => .branch .r3 23 12 14 23
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (tape : Bits) (pc : Fin 24) : NaturalState 24 :=
  ⟨heap,heap.length,r,[],pc,tape⟩

def signPC (a b : Bool) : Fin 24 := if a then (if b then 12 else 10) else if b then 8 else 12

def choicePC : Choice → Fin 24
  | .grid => 12
  | .gap => 13
  | .nilWord => 14

set_option maxHeartbeats 1600000 in
theorem natural_shift {heap : NaturalHeap} {r : Registers ℕ} {grid gap : Bits} {a b same edge : Bool}
    (bounds : CandidatePortGapProgram.InputBounds heap r.a grid gap)
    (relation : Flags heap r.b same edge) (signs : Flags heap r.c a b) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),BoolList (heap++ext) root (word grid gap a b same edge) ∧
      NaturalRun program (steps a b same) (state heap r tape 0) [] (state (heap++ext) (r.set .r3 root) tape 20) := by
  obtain ⟨g,c,pair,gridRep,gapRep⟩ := bounds
  obtain ⟨s,e,relations,sp,adj⟩ := relation
  obtain ⟨i,j,signPair,signA,signB⟩ := signs
  let ext : NaturalHeap := if choose a b same edge=.nilWord then [.nil] else []
  let root := match choose a b same edge with
    | .grid => g
    | .gap => c
    | .nilWord => heap.length
  refine ⟨ext,root,?_,?_⟩
  · cases h : choose a b same edge <;> simp [word,ext,root, *]
    exact .nil (by simp)
  · let afterSigns := r.set .r3 j
    let afterRelation := r.set .r3 (if a==b then j else if !a && !same then e else s)
    have signTrace : NaturalRun program 4 (state heap r tape 0) [] (state heap afterSigns tape (signPC a b)) := by
      apply ReferenceProgramSteps.sound
      cases a <;> cases b <;> simp [ReferenceProgramSteps.run,program,state,signPC,afterSigns,tickNatural,
        Registers.get,Registers.set,tagBranch,signPair,signA,signB]
    have relationTrace : NaturalRun program (relationSteps a b same) (state heap afterSigns tape (signPC a b)) []
        (state heap afterRelation tape (choicePC (choose a b same edge))) := by
      apply ReferenceProgramSteps.sound
      cases a <;> cases b <;> cases same <;> cases edge <;>
        simp [ReferenceProgramSteps.run,program,state,signPC,choicePC,relationSteps,choose,
          afterSigns,afterRelation,tickNatural,Registers.get,Registers.set,tagBranch, *]
    have finish : NaturalRun program 1 (state heap afterRelation tape (choicePC (choose a b same edge))) []
        (state (heap++ext) (r.set .r3 root) tape 20) := by
      apply ReferenceProgramSteps.sound
      cases ch : choose a b same edge <;>
        simp [ReferenceProgramSteps.run,program,state,choicePC,ext,root,afterRelation,tickNatural,
          Registers.get,Registers.set,allocateNatural,Recipe.cell,pair,ch]
    exact ConcreteExpressionProgram.append_run (ConcreteExpressionProgram.append_run signTrace relationTrace) finish

end DirectedFlowCutGap.CandidateShiftSelectProgram
