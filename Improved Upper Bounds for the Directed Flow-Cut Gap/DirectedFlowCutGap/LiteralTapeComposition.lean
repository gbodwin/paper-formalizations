import DirectedFlowCutGap.ControllerTapeModel
import DirectedFlowCutGap.ChargedUniformRounding
import DirectedFlowCutGap.ChargedCutSelection

/-! Exact tape sequencing for composing physical calls with tree specifications. -/

namespace DirectedFlowCutGap.LiteralTapeComposition

open BinaryArithmetic FiniteDrawTrees LazyFairBitTrees

def execute {A : Type} (T : ℕ) (tree : FiniteDrawTrees.Tree A) (tape : Bits) : Option (A × Bits) :=
  (EncodedSolverBits.run (lower T tree) tape).map (fun (a,(rest,_)) => (a,rest))

@[simp] theorem execute_pure {A : Type} (T : ℕ) (a : A) (tape : Bits) :
    execute T (.pure a) tape=some (a,tape) := rfl

theorem execute_map {A B : Type} (T : ℕ) (f : A → B) (tree : FiniteDrawTrees.Tree A) (tape : Bits) :
    execute T (map f tree) tape=(execute T tree tape).map (fun (a,rest) => (f a,rest)) := by
  unfold execute
  rw [show lower T (map f tree)=map f (lower T tree) from
    (ChargedUniformRounding.map_lower T f tree).symm,EncodedSolverBits.run_map]
  simp only [Option.map_map,Function.comp_def]

theorem execute_bind {A B : Type} (T : ℕ) (tree : FiniteDrawTrees.Tree A)
    (next : A → FiniteDrawTrees.Tree B) (tape : Bits) :
    execute T (tree >>= next) tape =
      (execute T tree tape).bind (fun (a,rest) => execute T (next a) rest) := by
  unfold execute
  rw [ControllerTapeModel.run_bind]
  cases first : EncodedSolverBits.run (lower T tree) tape with
  | none => rfl
  | some result =>
    rcases result with ⟨a,rest,reads⟩
    cases second : EncodedSolverBits.run (lower T (next a)) rest with
    | none => simp only [Option.bind_some,Option.map_some,second,Option.map_none]
    | some answer => rcases answer with ⟨b,tail,count⟩; simp only [Option.bind_some,Option.map_some,second]

end DirectedFlowCutGap.LiteralTapeComposition
