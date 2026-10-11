import DirectedFlowCutGap.InputExpressionProgram
import DirectedFlowCutGap.EncodedPackingBitBudget

/-! The displayed packing-prefix polynomial is now computed by one literal
finite instruction table from three self-delimited source words. Its result
is the same padded word as the previously checked Boolean expression. -/
namespace DirectedFlowCutGap.PackingBudgetProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def body : ConcreteExpressionProgram.Term :=
  ConcreteExpressionProgram.translate EncodedPackingBitBudget.body

def program := InputExpressionProgram.program body
def initial := InputExpressionProgram.initial body
def instructions := InputExpressionProgram.instructions body

def coefficient : ℕ := ConcreteExpressionBounds.terminalCoefficient
  (InputExpressionProgram.capacity body) (ConcreteExpressionBounds.cost body+20)

/-- Inputs, fixed literals, arithmetic calls, stack frames and the final
halt are all executed by the same concrete program. The sufficient random
prefix budget is computed, not supplied as a natural-valued operation. -/
theorem compute_budget (n b s suffix : Bits) :
    ∃ charge out, Run program (instructions n b s) charge
        (initial (SelfDelimitedWordProgram.encode n++SelfDelimitedWordProgram.encode b++
          SelfDelimitedWordProgram.encode s++suffix))
        ((SelfDelimitedWordProgram.encode n++SelfDelimitedWordProgram.encode b++
          SelfDelimitedWordProgram.encode s).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (EncodedPackingBitBudget.run n b s).1 ∧
      value (EncodedPackingBitBudget.run n b s).1 =
        (3*(value n)^2+1)*((3*(3*(value n)^2+2*value b+value n+3)+1)*
          QueryBudgetArithmetic.polynomial (24*(value n)^2))+
          (2*value b+value n+3)*(3*(value n)^2*(value s+1)+2) ∧
      ConcreteExpressionProgram.Inputs (eraseState out).heap (eraseState out).registers.a
        (eraseState out).registers.b (eraseState out).registers.c ![n,b,s] ∧
      out.source=suffix ∧
      out.pc=InputExpressionProgram.expressionLabel body (ConcreteExpressionProgram.exit body) ∧
      out.stack=[] ∧ value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ coefficient*(n.length+b.length+s.length+1)^6 := by
  obtain ⟨charge,out,run,word,old,source,pc,stack,_len,dense,halt,bound⟩ :=
    InputExpressionProgram.evaluate_from_source body n b s suffix
  refine ⟨charge,out,run,?_,EncodedPackingBitBudget.run_value n b s,old,source,pc,stack,dense,halt,?_⟩
  · simpa only [body,ConcreteExpressionProgram.evaluate_translate,EncodedPackingBitBudget.run] using word
  · exact bound.trans (InputExpressionProgram.total_bound body n b s)

end DirectedFlowCutGap.PackingBudgetProgram
