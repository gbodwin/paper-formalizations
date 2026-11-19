import DirectedFlowCutGap.CandidateRefreshProgram
import DirectedFlowCutGap.EpochSelectedRoundProgram
import DirectedFlowCutGap.AdaptiveGatesProgram

/-! Stored records shared by epoch iteration and stabilization. -/

namespace DirectedFlowCutGap.AdaptiveControllerStorage

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open RetainedMassTableProgram (DataRows TableAt pairOrder)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (EdgeList edgeList_extend)

def StateAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (d : Data n) (words : List (List Bits)) (bits : Bits) : Prop :=
  ∃ packed runtime context scale weights free,
    heap[root]?=some (.pair packed runtime) ∧ RoundStateUpdateProgram.UpdatedAt heap packed d ∧
    heap[runtime]?=some (.pair context scale) ∧ heap[context]?=some (.pair weights free) ∧
    TableAt heap weights words ∧ heap[free]?=some (.flag false) ∧ BoolList heap scale bits ∧ value bits=d.scale ∧
    DataRows d.weights words

def CacheAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (d : Data n) (optimum : ℕ) (candidate : Family n)
    (currentWords candidateWords : List (List Bits)) (scale : Bits) : Prop :=
  ∃ state best,heap[root]?=some (.pair state best) ∧ StateAt heap state d currentWords scale ∧
    CandidateRefreshProgram.Output heap best candidate optimum candidateWords

def Parameters {n L : ℕ} (heap : NaturalHeap) (root : ℕ) (adj : PairFlags n) (R M : Bits) : Prop :=
  ∃ static gates round refresh graph config pairs shared,
    heap[root]?=some (.pair static gates) ∧ heap[static]?=some (.pair round refresh) ∧
    heap[round]?=some (.pair graph config) ∧ heap[refresh]?=some (.pair pairs shared) ∧
    AdaptiveGatesProgram.Parameters heap gates R M ∧
    RoundInputPackProgram.GraphAt heap graph (EpochSelectedRoundProgram.enumeration n) adj ∧
    EpochSelectedRoundProgram.config heap config n ∧ EdgeList heap pairs ((pairOrder n).map labelPair) ∧
    CandidateFamilyProgram.Shared heap shared ⟨adj,Vector.replicate n false⟩ n.bits L.bits

theorem updated_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {d : Data n}
    (h : RoundStateUpdateProgram.UpdatedAt heap root d) (ext : NaturalHeap) :
    RoundStateUpdateProgram.UpdatedAt (heap++ext) root d := by
  obtain ⟨m,c,b,read,masks,mass,value⟩ := h
  exact ⟨m,c,b,lookup_extend read ext,RoundInputPackProgram.masks_extend masks ext,boolList_extend mass ext,value⟩

theorem state_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {d : Data n} {words : List (List Bits)} {bits : Bits}
    (h : StateAt heap root d words bits) (ext : NaturalHeap) : StateAt (heap++ext) root d words bits := by
  obtain ⟨p,r,c,s,w,f,outer,output,runtime,context,table,free,scale,width,rows⟩ := h
  exact ⟨p,r,c,s,w,f,lookup_extend outer ext,updated_extend output ext,lookup_extend runtime ext,lookup_extend context ext,
    RoundInputPackProgram.weights_extend table ext,lookup_extend free ext,boolList_extend scale ext,width,rows⟩

theorem candidate_extend {n : ℕ} {heap : NaturalHeap} {root optimum : ℕ} {data : Family n} {words : List (List Bits)}
    (h : CandidateRefreshProgram.Output heap root data optimum words) (ext : NaturalHeap) :
    CandidateRefreshProgram.Output (heap++ext) root data optimum words := by
  obtain ⟨w,m,b,pair,table,rows,word,value⟩ := h
  exact ⟨w,m,b,lookup_extend pair ext,RoundInputPackProgram.weights_extend table ext,rows,boolList_extend word ext,value⟩

theorem cache_extend {n : ℕ} {heap : NaturalHeap} {root optimum : ℕ} {d : Data n} {candidate : Family n}
    {currentWords candidateWords : List (List Bits)} {bits : Bits}
    (h : CacheAt heap root d optimum candidate currentWords candidateWords bits)
    (ext : NaturalHeap) : CacheAt (heap++ext) root d optimum candidate currentWords candidateWords bits := by
  obtain ⟨s,c,read,state,output⟩ := h
  exact ⟨s,c,lookup_extend read ext,state_extend state ext,candidate_extend output ext⟩

theorem shared_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : EncodedCandidateCapacity.Input n} {vertices grid : Bits}
    (h : CandidateFamilyProgram.Shared heap root D vertices grid) (ext : NaturalHeap) :
    CandidateFamilyProgram.Shared (heap++ext) root D vertices grid := by
  obtain ⟨g,r,l,j,us,outer,rest,graph,labels,len,word⟩ := h
  exact ⟨g,r,l,j,us,lookup_extend outer ext,lookup_extend rest ext,CandidateDemandRowProgram.graph_extend graph ext,
    GraphDiscoveryProgram.vertices_extend labels ext,len,boolList_extend word ext⟩

theorem parameters_extend {n L : ℕ} {heap : NaturalHeap} {root : ℕ} {adj : PairFlags n} {R M : Bits}
    (h : Parameters (L:=L) heap root adj R M) (ext : NaturalHeap) : Parameters (L:=L) (heap++ext) root adj R M := by
  obtain ⟨static,gates,round,refresh,graph,config,pairs,shared,outer,split,roundAt,refreshAt,gate,graphRep,roundConfig,labels,solver⟩ := h
  obtain ⟨e,m,readGraph,vertices,matrix⟩ := graphRep
  obtain ⟨size,one,readConfig,nRep,truth⟩ := roundConfig
  exact ⟨static,gates,round,refresh,graph,config,pairs,shared,lookup_extend outer ext,lookup_extend split ext,
    lookup_extend roundAt ext,lookup_extend refreshAt ext,AdaptiveGatesProgram.parameters_extend gate ext,
    ⟨e,m,lookup_extend readGraph ext,GraphDiscoveryProgram.vertices_extend vertices ext,GraphAdjacencyProgram.matrix_extend matrix ext⟩,
    ⟨size,one,lookup_extend readConfig ext,boolList_extend nRep ext,boolList_extend truth ext⟩,
    edgeList_extend labels ext,shared_extend solver ext⟩

end DirectedFlowCutGap.AdaptiveControllerStorage
