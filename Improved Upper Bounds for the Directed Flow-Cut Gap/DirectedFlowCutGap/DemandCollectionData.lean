import DirectedFlowCutGap.ActualGraphShortest
import DirectedFlowCutGap.CostedCandidateSelection

/-! Literal demand occurrences and shared graph inputs. No discovered path or
cost is present in the input demand list. Each output payload pairs the original
list-node pointer with the path record returned by the actual shortest program. -/
namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

structure Demand where
  sourceWord : Bits
  targetWord : Bits
  record : ℕ
  occurrence : ℕ

def StoredDemand (heap : NaturalHeap) (x : Demand) : Prop :=
  ∃ sr tr,heap[x.record]?=some (.pair sr tr) ∧
    BoolList heap sr x.sourceWord ∧ BoolList heap tr x.targetWord

inductive DemandList (heap : NaturalHeap) : ℕ → List Demand → Prop
  | nil {p} : heap[p]?=some .nil → DemandList heap p []
  | cons {p tail x xs} : p=x.occurrence → heap[p]?=some (.pair x.record tail) →
      StoredDemand heap x → DemandList heap tail xs → DemandList heap p (x::xs)

def Shared (heap : NaturalHeap) (p : ℕ) (vs adjacency : List Bits) (rows : List Fraction) : Prop :=
  ∃ enumRoot bundle matrix table,heap[p]?=some (.pair enumRoot bundle) ∧
    heap[bundle]?=some (.pair matrix table) ∧ GraphDiscoveryProgram.Vertices heap enumRoot vs ∧
    GraphAdjacencyProgram.Matrix heap matrix adjacency ∧
    WordPairTableRead.Table heap table (IndexedRationalRead.fields rows)

theorem demand_extend {heap : NaturalHeap} {x : Demand} (h : StoredDemand heap x)
    (ext : NaturalHeap) : StoredDemand (heap++ext) x := by
  obtain ⟨sr,tr,hp,hs,ht⟩ := h
  exact ⟨sr,tr,lookup_extend hp ext,boolList_extend hs ext,boolList_extend ht ext⟩

theorem demands_extend {heap : NaturalHeap} {p : ℕ} {xs : List Demand}
    (h : DemandList heap p xs) (ext : NaturalHeap) : DemandList (heap++ext) p xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons he hp hx _ ih => exact .cons he (lookup_extend hp ext) (demand_extend hx ext) ih

theorem shared_extend {heap : NaturalHeap} {p : ℕ} {vs adjacency : List Bits} {rows : List Fraction}
    (h : Shared heap p vs adjacency rows) (ext : NaturalHeap) : Shared (heap++ext) p vs adjacency rows := by
  obtain ⟨vr,b,m,t,hp,hb,hv,ha,hr⟩ := h
  exact ⟨vr,b,m,t,lookup_extend hp ext,lookup_extend hb ext,
    GraphDiscoveryProgram.vertices_extend hv ext,GraphAdjacencyProgram.matrix_extend ha ext,
    BinaryIndexedPairRead.table_extend hr ext⟩

def query (vs adjacency : List Bits) (rows : List Fraction) (x : Demand) : Option Walk :=
  GraphRecoveryController.result vs adjacency rows x.sourceWord x.targetWord x.sourceWord

def querySteps (vs adjacency : List Bits) (rows : List Fraction) (x : Demand) : ℕ :=
  GraphRecoveryController.steps vs adjacency rows x.sourceWord x.targetWord x.sourceWord

def queryCells (vs adjacency : List Bits) (rows : List Fraction) (x : Demand) : ℕ :=
  GraphRecoveryController.cells vs adjacency rows x.sourceWord x.targetWord x.sourceWord

def steps (vs adjacency : List Bits) (rows : List Fraction) : List Demand → ℕ
  | [] => 3
  | x::xs => steps vs adjacency rows xs+querySteps vs adjacency rows x+
      match query vs adjacency rows x with | none => 32 | some _ => 37

def cells (vs adjacency : List Bits) (rows : List Fraction) : List Demand → ℕ
  | [] => 1
  | x::xs => cells vs adjacency rows xs+queryCells vs adjacency rows x+
      match query vs adjacency rows x with | none => 5 | some _ => 8

structure Record where
  demand : Demand
  path : Walk
  item : RetainedArgminProgram.Item

def records (vs adjacency : List Bits) (rows : List Fraction) (next : ℕ) : List Demand → List Record
  | [] => []
  | x::xs => match query vs adjacency rows x with
      | none => records vs adjacency rows next xs
      | some q =>
        let payload := next+cells vs adjacency rows xs+5+queryCells vs adjacency rows x
        ⟨x,q,⟨q.cost,payload,payload+1⟩⟩::records vs adjacency rows next xs

def StoredRecord (heap : NaturalHeap) (z : Record) : Prop :=
  RetainedArgminProgram.StoredItem heap z.item.address z.item ∧
    z.item.score=z.path.cost ∧ ∃ pathRoot,
      heap[z.item.payload]?=some (.pair z.demand.occurrence pathRoot) ∧ StoredWalk heap pathRoot z.path

inductive RecordList (heap : NaturalHeap) : ℕ → List Record → Prop
  | nil {p} : heap[p]?=some .nil → RecordList heap p []
  | cons {p tail z zs} : heap[p]?=some (.pair z.item.address tail) →
      StoredRecord heap z → RecordList heap tail zs → RecordList heap p (z::zs)

theorem record_extend {heap : NaturalHeap} {z : Record} (h : StoredRecord heap z)
    (ext : NaturalHeap) : StoredRecord (heap++ext) z := by
  obtain ⟨hi,hs,p,hp,hw⟩ := h
  exact ⟨RetainedArgminProgram.stored_extend hi ext,hs,p,lookup_extend hp ext,walk_extend hw ext⟩

theorem records_extend {heap : NaturalHeap} {p : ℕ} {zs : List Record}
    (h : RecordList heap p zs) (ext : NaturalHeap) : RecordList (heap++ext) p zs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hz _ ih => exact .cons (lookup_extend hp ext) (record_extend hz ext) ih

theorem item_list {heap : NaturalHeap} {p : ℕ} {zs : List Record} (h : RecordList heap p zs) :
    RetainedArgminProgram.ItemList heap p (zs.map Record.item) := by
  induction h with
  | nil hp => exact .nil hp
  | cons hp hz _ ih => exact .cons hp hz.1 ih

end DirectedFlowCutGap.DemandCollection
