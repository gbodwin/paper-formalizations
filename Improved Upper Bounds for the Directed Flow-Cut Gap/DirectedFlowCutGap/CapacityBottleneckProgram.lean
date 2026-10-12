import DirectedFlowCutGap.ActualOracleMask

/-! A literal aligned traversal of the actual internal-mask flags, vertex
word pointers and separate capacity table builds the stable-selector input. -/
namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

structure Slot where
  enabled : Bool
  word : Bits
  vertexRoot : ℕ
  score : Fraction

inductive Parallel (heap : NaturalHeap) : ℕ → ℕ → ℕ → List Slot → Prop
  | nil {m v t} : heap[m]?=some .nil → heap[v]?=some .nil → heap[t]?=some .nil → Parallel heap m v t []
  | cons {m v t f mt vt score tt x xs} :
      heap[m]?=some (.pair f mt) → heap[f]?=some (.flag x.enabled) →
      heap[v]?=some (.pair x.vertexRoot vt) → BoolList heap x.vertexRoot x.word →
      heap[t]?=some (.pair score tt) → Stored heap score x.score →
      Parallel heap mt vt tt xs → Parallel heap m v t (x::xs)
def Input (heap : NaturalHeap) (mask context : ℕ) (xs : List Slot) : Prop :=
  ∃ v t,heap[context]?=some (.pair v t) ∧ Parallel heap mask v t xs

def steps : List Slot → ℕ
  | [] => 3
  | x::xs => steps xs+(if x.enabled then 24 else 16)
def cells : List Slot → ℕ
  | [] => 1
  | x::xs => cells xs+(if x.enabled then 5 else 3)
def items (next : ℕ) : List Slot → List RetainedArgminProgram.Item
  | [] => []
  | x::xs => if x.enabled then ⟨x.score,x.vertexRoot,next+cells xs+3⟩::items (next+2) xs
    else items (next+2) xs

def label (pc : Fin 194) : Fin 244 := ⟨pc.val,by omega⟩
def program : Program 244 := fun pc =>
  if h : pc.val<194 then
    ReferenceProgramLabels.instruction label (RetainedArgminProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 200 => .branch .r0 201 243 243 203
  | 201 => .make .r3 .nil 202
  | 202 => .ret .r3
  | 203 => .make .r2 (.pair .r0 .r1) 204
  | 204 => .field .r0 .r0 true 205
  | 205 => .field .r3 .r1 false 206
  | 206 => .field .r3 .r3 true 207
  | 207 => .field .r1 .r1 true 208
  | 208 => .field .r1 .r1 true 209
  | 209 => .make .r1 (.pair .r3 .r1) 210
  | 210 => .call 200 211 .r3
  | 211 => .make .r2 (.pair .r2 .r3) 212
  | 212 => .field .r0 .r2 false 213
  | 213 => .field .r0 .r0 false 214
  | 214 => .field .r0 .r0 false 215
  | 215 => .branch .r0 243 216 222 243
  | 216 => .field .r3 .r2 true 217
  | 217 => .ret .r3
  | 222 => .field .r0 .r2 false 223
  | 223 => .field .r0 .r0 true 224
  | 224 => .field .r1 .r0 false 225
  | 225 => .field .r1 .r1 false 226
  | 226 => .field .r0 .r0 true 227
  | 227 => .field .r0 .r0 false 228
  | 228 => .make .r0 (.pair .r0 .r1) 229
  | 229 => .field .r3 .r2 true 230
  | 230 => .make .r3 (.pair .r0 .r3) 231
  | 231 => .ret .r3
  | 236 => .call 200 237 .r3
  | 240 => .call 200 241 .r3
  | 241 => .move .r0 .r3 178
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 244)) (source : Bits) (pc : Fin 244) : NaturalState 244 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
theorem slots (pc : Fin 194) :
    program (label pc)=ReferenceProgramLabels.instruction label (RetainedArgminProgram.program pc) := by
  simp [program,label,pc.isLt]
theorem run_append {s u v : NaturalState 244} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

theorem parallel_extend {heap : NaturalHeap} {m v t : ℕ} {xs : List Slot}
    (h : Parallel heap m v t xs) (extra : NaturalHeap) : Parallel (heap++extra) m v t xs := by
  induction h with
  | nil hm hv ht => exact .nil (lookup_extend hm extra) (lookup_extend hv extra) (lookup_extend ht extra)
  | cons hm hf hv hw ht hq _ ih =>
    exact .cons (lookup_extend hm extra) (lookup_extend hf extra) (lookup_extend hv extra)
      (boolList_extend hw extra) (lookup_extend ht extra) (stored_extend hq extra) ih

theorem input_extend {heap : NaturalHeap} {m c : ℕ} {xs : List Slot}
    (h : Input heap m c xs) (extra : NaturalHeap) : Input (heap++extra) m c xs := by
  obtain ⟨v,t,hp,hs⟩ := h
  exact ⟨v,t,lookup_extend hp extra,parallel_extend hs extra⟩

end DirectedFlowCutGap.CapacityBottleneck
