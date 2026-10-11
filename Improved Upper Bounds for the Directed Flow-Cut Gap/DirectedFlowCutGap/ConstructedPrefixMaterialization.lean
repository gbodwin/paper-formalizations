import DirectedFlowCutGap.BinaryCounterMaterialization
import DirectedFlowCutGap.ReferencePrefixMaterialization

/-! An actual binary input length now supplies the counter required by the
fixed source-materialization program. Preparation uses the preceding charged
Boolean/list routines; instruction-language compilation of that preparation
and acquisition of the incoming word/source remain separate. -/
namespace DirectedFlowCutGap.ConstructedPrefixMaterialization
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryCounterMaterialization

def initial (word source : Bits) : BitState 5 × ℕ :=
  let s := prepare word
  (⟨s.heap,s.next,⟨[],s.root,[],[]⟩,[],0,source⟩,s.operations+12)

def preparationBound (word : Bits) : ℕ :=
  128*(value word+1)^3+4*value word+4*word.length+17

theorem initial_spec (word source : Bits) :
    (initial word source).1.Bounded (2*value word+2) (2*value word+2) ∧
    value (initial word source).1.next=(initial word source).1.heap.length ∧
    BoolList (eraseState (initial word source).1).heap
      (eraseState (initial word source).1).registers.a [] ∧
    IndexSpine (eraseState (initial word source).1).heap
      (eraseState (initial word source).1).registers.b (value word) ∧
    (initial word source).2≤preparationBound word := by
  obtain ⟨hlen,hn,_,spine,nilTable,hw,hr,hh,hc⟩ := prepare_spec word
  refine ⟨?_,hn,nilTable,spine,?_⟩
  · simp only [initial,State.Bounded,State.records,List.length_nil,Nat.add_zero,
      Registers.All,List.not_mem_nil,false_implies]
    exact ⟨by rw [hlen],hw.trans (by omega),heapBound_mono hh (by omega),
      ⟨by omega,hr.trans (by omega),by omega,by omega⟩,fun _ => trivial⟩
  · change (prepare word).operations+12≤_
    unfold preparationBound
    omega

/-- All representation and width premises are supplied by the actual binary
counter constructor. The same source prefix is consumed and its suffix kept. -/
theorem materialize (word source : Bits) (enough : value word ≤ source.length) :
    ∃ charge out,
      Run ReferencePrefixMaterialization.program (4*value word+1) charge
        (initial word source).1 ((source.take (value word)).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a
        (source.take (value word)).reverse ∧
      out.source=source.drop (value word) ∧ out.pc=4 ∧
      out.Bounded ((2*value word+2)+(4*value word+1))
        ((2*value word+2)+(4*value word+1)) ∧
      (attempt ReferencePrefixMaterialization.program out).result=none ∧
      (initial word source).2+charge+
        (attempt ReferencePrefixMaterialization.program out).operations≤
          preparationBound word+
            completeBound 5 (2*value word+2) (2*value word+2) (4*value word+1) := by
  obtain ⟨bounded,hn,table,counter,cost⟩ := initial_spec word source
  obtain ⟨charge,out,run,rep,src,pc,bound,halt,hc⟩ :=
    ReferencePrefixMaterialization.materialize_bit (initial word source).1
      bounded rfl hn table counter enough
  refine ⟨charge,out,run,?_,src,pc,bound,halt,?_⟩
  · simpa [initial] using rep
  · omega

end DirectedFlowCutGap.ConstructedPrefixMaterialization
