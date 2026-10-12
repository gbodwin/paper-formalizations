import DirectedFlowCutGap.CostedSupportExecution
import DirectedFlowCutGap.GraphMinimizeConstruction

/-! Actual synchronous discovery followed by literal support recovery. A missing
minimizer returns its same nil. A present minimizer supplies its own edge-list
root to an internally constructed recovery context in the same heap. -/
namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

def discoveryLabel (pc : Fin 720) : Fin 1344 := ⟨pc.val,by omega⟩
def recoveryLabel (pc : Fin 592) : Fin 1344 := ⟨pc.val+720,by omega⟩
def program : Program 1344 := fun pc =>
  if pc.val=719 ∨ pc.val=1311 then .ret .r3
  else if h : pc.val<720 then
    ReferenceProgramLabels.instruction discoveryLabel (GraphDiscoveryProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<1312 then
    ReferenceProgramLabels.instruction recoveryLabel (CostedSupportProgram.program ⟨pc.val-720,by omega⟩)
  else match pc.val with
  | 1312 => .call 717 1313 .r3
  | 1313 => .branch .r3 1341 1343 1343 1314
  | 1314 => .field .r3 .r3 false 1315
  | 1315 => .field .r2 .r1 true 1316
  | 1316 => .field .r2 .r2 true 1317
  | 1317 => .field .r0 .r2 false 1318
  | 1318 => .make .r0 (.pair .r0 .r3) 1319
  | 1319 => .field .r3 .r1 true 1320
  | 1320 => .field .r3 .r3 false 1321
  | 1321 => .make .r0 (.pair .r3 .r0) 1322
  | 1322 => .field .r3 .r1 false 1323
  | 1323 => .make .r0 (.pair .r3 .r0) 1324
  | 1324 => .field .r2 .r2 true 1325
  | 1325 => .make .r1 (.pair .r0 .r2) 1326
  | 1326 => .field .r0 .r0 true 1327
  | 1327 => .field .r0 .r0 false 1328
  | 1328 => .field .r2 .r2 true 1329
  | 1329 => .call 1310 1330 .r3
  | 1330 => .ret .r3
  | 1341 => .ret .r3
  | 1342 => .call 1312 1343 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 1344)) (source : Bits) (pc : Fin 1344) : NaturalState 1344 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def result (vs adjacency : List Bits) (rows : List Fraction) (sw target u : Bits) : Option Walk :=
  (GraphDiscoveryProgram.minimize vs adjacency rows sw target u).map
    (fun q => CostedSupportProgram.result vs adjacency q.edges sw target rows)

def finishSteps (vs adjacency : List Bits) (rows : List Fraction) (sw target : Bits) : Option Walk → ℕ
  | none => 2
  | some q => CostedSupportProgram.steps vs adjacency q.edges sw target rows+20

def steps (vs adjacency : List Bits) (rows : List Fraction) (sw target u : Bits) : ℕ :=
  GraphDiscoveryProgram.minimizeSteps vs adjacency rows sw target u+3+
    finishSteps vs adjacency rows sw target (GraphDiscoveryProgram.minimize vs adjacency rows sw target u)

def finishCells (vs adjacency : List Bits) (rows : List Fraction) (sw target : Bits) : Option Walk → ℕ
  | none => 0
  | some q => CostedSupportProgram.cells vs adjacency q.edges sw target rows+4

def cells (vs adjacency : List Bits) (rows : List Fraction) (sw target u : Bits) : ℕ :=
  GraphDiscoveryProgram.minimizeCells vs adjacency rows sw target u+
    finishCells vs adjacency rows sw target (GraphDiscoveryProgram.minimize vs adjacency rows sw target u)

theorem discovery_slots (pc : Fin 720) (h : GraphDiscoveryProgram.program pc≠.halt) :
    program (discoveryLabel pc)=ReferenceProgramLabels.instruction discoveryLabel (GraphDiscoveryProgram.program pc) := by
  by_cases hp : pc.val=719
  · have he : pc=719 := Fin.ext hp
    subst pc;simp [GraphDiscoveryProgram.program] at h
  · simp [program,discoveryLabel,pc.isLt,hp,show ¬pc.val=1311 by omega]

theorem recovery_slots (pc : Fin 592) (h : CostedSupportProgram.program pc≠.halt) :
    program (recoveryLabel pc)=ReferenceProgramLabels.instruction recoveryLabel (CostedSupportProgram.program pc) := by
  by_cases hp : pc.val=591
  · have he : pc=591 := Fin.ext hp
    subst pc;simp [CostedSupportProgram.program] at h
  · simp [program,recoveryLabel,show ¬pc.val+720=719 by omega,show ¬pc.val+720=1311 by omega,
      show ¬pc.val+720<720 by omega,show pc.val+720<1312 by omega]

theorem run_append {s u v : NaturalState 1344} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.GraphRecoveryController
