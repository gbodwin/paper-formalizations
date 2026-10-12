import DirectedFlowCutGap.GraphDiscoveryCalls

/-! Reconstructed literal forward-updating support search. This draft is outside
the published checkpoint and requires fresh verification after recovery. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

abbrev Code := Bits × List (Bits × Bits)
abbrev Vertices := GraphDiscoveryProgram.Vertices

def same (u v : Bits) : Bool := decide (BinaryComparisonProgram.order u v = .eq)
def edgeEq (e f : Bits × Bits) : Bool := same e.1 f.1 && same e.2 f.2
def member (e : Bits × Bits) : List (Bits × Bits) → Bool
  | [] => false
  | f::fs => if edgeEq f e then true else member e fs
def support (adjacency : List Bits) (es : List (Bits × Bits)) (u v : Bits) : Bool :=
  GraphRelaxationProgram.adjacent adjacency u v && member (u,v) es
def lookup (u : Bits) : List Code → Option Code
  | [] => none
  | x::xs => if same x.1 u then some x else lookup u xs
def predecessor (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) : List Code → Option Code
  | [] => none
  | x::xs => if support adjacency es u x.1 then some x else predecessor adjacency es u xs
def visit (adjacency : List Bits) (es : List (Bits × Bits)) (u : Bits) (xs : List Code) : List Code :=
  match lookup u xs with
  | some _ => xs
  | none => match predecessor adjacency es u xs with
      | none => xs
      | some x => (u,(u,x.1)::x.2)::xs
def pass (adjacency : List Bits) (es : List (Bits × Bits)) : List Bits → List Code → List Code
  | [],xs => xs
  | u::us,xs => pass adjacency es us (visit adjacency es u xs)
def rounds (vs : List Bits) (adjacency : List Bits) (es : List (Bits × Bits)) (target : Bits) : List Bits → List Code
  | [] => [(target,[])]
  | _::fuel => pass adjacency es vs (rounds vs adjacency es target fuel)
def search (vs : List Bits) (adjacency : List Bits) (es : List (Bits × Bits)) (source target : Bits) : List (Bits × Bits) :=
  match lookup source (rounds vs adjacency es target vs) with
  | none => []
  | some x => x.2

def StoredCode (heap : NaturalHeap) (p : ℕ) (x : Code) : Prop :=
  ∃ vertex edges,heap[p]?=some (.pair vertex edges) ∧ BoolList heap vertex x.1 ∧ EdgeList heap edges x.2
inductive Codes (heap : NaturalHeap) : ℕ → List Code → Prop
  | nil {p} : heap[p]?=some .nil → Codes heap p []
  | cons {p head tail x xs} : heap[p]?=some (.pair head tail) → StoredCode heap head x →
      Codes heap tail xs → Codes heap p (x::xs)
def StoredOption (heap : NaturalHeap) (p : ℕ) : Option Code → Prop
  | none => heap[p]?=some .nil
  | some x => StoredCode heap p x
def SupportContext (heap : NaturalHeap) (p : ℕ) (adjacency : List Bits) (es : List (Bits × Bits)) : Prop :=
  ∃ matrix edges,heap[p]?=some (.pair matrix edges) ∧
    GraphAdjacencyProgram.Matrix heap matrix adjacency ∧ EdgeList heap edges es

def adjLabel (pc : Fin 36) : Fin 280 := ⟨pc.val,by omega⟩
def cmpLabel (pc : Fin 48) : Fin 280 := ⟨pc.val+36,by omega⟩
def program : Program 280 := fun pc =>
  if pc.val=35 ∨ pc.val=83 then .ret .r3
  else if h : pc.val<36 then
    ReferenceProgramLabels.instruction adjLabel (GraphAdjacencyProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<84 then
    ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program ⟨pc.val-36,by omega⟩)
  else match pc.val with
  | 84 => .call 36 83 .r3
  | 90 => .branch .r0 91 279 279 93
  | 91 => .make .r3 (.flag false) 92
  | 92 => .ret .r3
  | 93 => .move .r2 .r0 94
  | 94 => .field .r0 .r0 false 95
  | 95 => .call 100 96 .r3
  | 96 => .branch .r3 279 97 99 279
  | 97 => .field .r0 .r2 true 98
  | 98 => .call 90 99 .r3
  | 99 => .ret .r3
  | 100 => .make .r2 (.pair .r0 .r1) 101
  | 101 => .field .r0 .r0 false 102
  | 102 => .field .r1 .r1 false 103
  | 103 => .call 84 104 .r3
  | 104 => .branch .r3 105 114 114 279
  | 105 => .field .r0 .r2 false 106
  | 106 => .field .r0 .r0 true 107
  | 107 => .field .r1 .r2 true 108
  | 108 => .field .r1 .r1 true 109
  | 109 => .call 84 110 .r3
  | 110 => .branch .r3 112 114 114 279
  | 112 => .make .r3 (.flag true) 113
  | 113 => .ret .r3
  | 114 => .make .r3 (.flag false) 115
  | 115 => .ret .r3
  | 120 => .make .r2 (.pair .r0 .r1) 121
  | 121 => .field .r3 .r0 true 122
  | 122 => .field .r0 .r0 false 123
  | 123 => .field .r1 .r1 false 124
  | 124 => .make .r1 (.pair .r1 .r3) 125
  | 125 => .call 34 126 .r3
  | 126 => .branch .r3 279 139 127 279
  | 127 => .field .r0 .r2 true 128
  | 128 => .field .r0 .r0 true 129
  | 129 => .field .r1 .r2 false 130
  | 130 => .call 90 139 .r3
  | 139 => .ret .r3
  | 150 => .branch .r0 151 279 279 153
  | 151 => .make .r3 .nil 152
  | 152 => .ret .r3
  | 153 => .move .r2 .r0 154
  | 154 => .field .r0 .r0 false 155
  | 155 => .field .r0 .r0 false 156
  | 156 => .call 84 157 .r3
  | 157 => .branch .r3 158 160 160 279
  | 158 => .field .r3 .r2 false 159
  | 159 => .ret .r3
  | 160 => .field .r0 .r2 true 161
  | 161 => .call 150 162 .r3
  | 162 => .ret .r3
  | 170 => .branch .r0 151 279 279 171
  | 171 => .make .r2 (.pair .r0 .r1) 172
  | 172 => .field .r0 .r0 false 173
  | 173 => .field .r0 .r0 false 174
  | 174 => .field .r3 .r1 false 175
  | 175 => .make .r0 (.pair .r3 .r0) 176
  | 176 => .field .r1 .r1 true 177
  | 177 => .call 120 178 .r3
  | 178 => .branch .r3 279 179 185 279
  | 179 => .field .r0 .r2 false 180
  | 180 => .field .r0 .r0 true 181
  | 181 => .field .r1 .r2 true 182
  | 182 => .call 170 183 .r3
  | 183 => .ret .r3
  | 185 => .field .r0 .r2 false 186
  | 186 => .field .r3 .r0 false 187
  | 187 => .ret .r3
  | 190 => .make .r2 (.pair .r0 .r1) 191
  | 191 => .field .r0 .r1 false 192
  | 192 => .field .r1 .r2 false 193
  | 193 => .call 150 194 .r3
  | 194 => .branch .r3 195 279 279 215
  | 195 => .field .r0 .r2 true 196
  | 196 => .field .r0 .r0 false 197
  | 197 => .field .r1 .r2 false 198
  | 198 => .field .r3 .r2 true 199
  | 199 => .field .r3 .r3 true 200
  | 200 => .make .r1 (.pair .r1 .r3) 201
  | 201 => .call 170 202 .r3
  | 202 => .branch .r3 215 279 279 203
  | 203 => .field .r0 .r2 false 204
  | 204 => .field .r1 .r3 false 205
  | 205 => .make .r1 (.pair .r0 .r1) 206
  | 206 => .field .r3 .r3 true 207
  | 207 => .make .r3 (.pair .r1 .r3) 208
  | 208 => .make .r0 (.pair .r0 .r3) 209
  | 209 => .field .r1 .r2 true 210
  | 210 => .field .r1 .r1 false 211
  | 211 => .make .r3 (.pair .r0 .r1) 212
  | 212 => .ret .r3
  | 215 => .field .r3 .r2 true 216
  | 216 => .field .r3 .r3 false 217
  | 217 => .ret .r3
  | 220 => .branch .r0 221 279 279 224
  | 221 => .field .r3 .r1 false 222
  | 222 => .ret .r3
  | 224 => .make .r2 (.pair .r0 .r1) 225
  | 225 => .field .r0 .r0 false 226
  | 226 => .call 190 227 .r3
  | 227 => .field .r0 .r2 true 228
  | 228 => .field .r0 .r0 true 229
  | 229 => .make .r1 (.pair .r3 .r0) 230
  | 230 => .field .r0 .r2 false 231
  | 231 => .field .r0 .r0 true 232
  | 232 => .call 220 233 .r3
  | 233 => .ret .r3
  | 240 => .branch .r0 241 279 279 246
  | 241 => .make .r3 .nil 242
  | 242 => .field .r0 .r1 false 243
  | 243 => .make .r0 (.pair .r0 .r3) 244
  | 244 => .make .r3 (.pair .r0 .r3) 245
  | 245 => .ret .r3
  | 246 => .field .r0 .r0 true 247
  | 247 => .call 240 248 .r3
  | 248 => .field .r0 .r1 true 249
  | 249 => .field .r2 .r0 true 250
  | 250 => .field .r0 .r0 false 251
  | 251 => .make .r1 (.pair .r3 .r2) 252
  | 252 => .call 220 253 .r3
  | 253 => .ret .r3
  | 260 => .call 240 261 .r3
  | 261 => .move .r0 .r3 262
  | 262 => .move .r1 .r2 263
  | 263 => .call 150 264 .r3
  | 264 => .branch .r3 265 279 279 267
  | 265 => .ret .r3
  | 267 => .field .r3 .r3 true 268
  | 268 => .ret .r3
  | 270 => .call 260 279 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 280)) (source : Bits) (pc : Fin 280) : NaturalState 280 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem adj_slots (pc : Fin 36) (h : GraphAdjacencyProgram.program pc≠.halt) :
    program (adjLabel pc)=ReferenceProgramLabels.instruction adjLabel (GraphAdjacencyProgram.program pc) := by
  by_cases hp : pc.val=35
  · have he : pc=35 := Fin.ext hp
    subst pc;simp [GraphAdjacencyProgram.program] at h
  · simp [program,adjLabel,pc.isLt,hp,show ¬pc.val=83 by omega]
theorem cmp_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (cmpLabel pc)=ReferenceProgramLabels.instruction cmpLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have he : pc=47 := Fin.ext hp
    subst pc;simp [BinaryComparisonProgram.program] at h
  · simp [program,cmpLabel,show ¬pc.val+36=35 by omega,show ¬pc.val+36=83 by omega,
      show ¬pc.val+36<36 by omega,show pc.val+36<84 by omega]

theorem run_append {s u v : NaturalState 280} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

end DirectedFlowCutGap.SupportRecoveryProgram
