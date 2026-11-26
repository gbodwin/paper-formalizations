import OnlineReachabilityPreservers.SteinerBinaryForestLabelsWork
import OnlineReachabilityPreservers.SteinerBinaryWeightedRunWork
import OnlineReachabilityPreservers.SteinerForestAttachmentsWork
import OnlineReachabilityPreservers.SteinerForestLabelWork

/-! Run the binary weighted cover with the metric forest's own costs and attachments. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} {h : ℕ} [LinearOrder V] [Fintype V]

local instance forestFractionalVertexDecidableEq : DecidableEq (ForestNetworkVertex V h) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V h)).toDecidableEq

private def forestPaidCostWithWork (paid : Arcs (ForestNetworkVertex V h)) (read : V × V → ℕ × ℕ)
    (e : ForestNetworkVertex V h × ForestNetworkVertex V h) : Option ℕ × ℕ :=
  let present := memFinsetWithWordWork e paid
  if present.1 then
    let cost := forestDistanceWeightWithWordWork read ((ofLex e.1).2,(ofLex e.2).2)
    (some cost.1,present.2+cost.2+8)
  else (none,present.2+4)

private theorem forestPaidCostWithWork_spec (G : Arcs V) (paid : Arcs (ForestNetworkVertex V h))
    (read : V × V → ℕ × ℕ) (fee : ℕ) (value : ∀ e, (read e).1 = hops G e.1 e.2)
    (work : ∀ e, (read e).2 ≤ fee) (e : ForestNetworkVertex V h × ForestNetworkVertex V h) :
    let out := forestPaidCostWithWork paid read e
    out.1 = (if e ∈ paid then some (forestNetworkWeight G e) else none) ∧
    out.2 ≤ 12*paid.card+10*h+8*fee+53 := by
  let present := memFinsetWithWordWork e paid
  let endpoints := ((ofLex e.1).2,(ofLex e.2).2)
  let cost := forestDistanceWeightWithWordWork read endpoints
  obtain ⟨test,look⟩ := memFinsetWithWordWork_spec e paid
  obtain ⟨distance,price⟩ := forestDistanceWeightWithWordWork_spec read fee work endpoints
  change present.2 ≤ _ at look
  change cost.2 ≤ _ at price
  have exactWeight : cost.1 = forestNetworkWeight G e := distance.trans (value _)
  dsimp only [forestPaidCostWithWork]
  rw [test]
  by_cases on : e ∈ paid
  · simp only [on,decide_true,ite_true]
    exact ⟨congrArg some exactWeight,by change present.2+cost.2+8 ≤ _; omega⟩
  · simp only [on,decide_false,Bool.false_eq_true,ite_false,true_and]
    change present.2+4 ≤ _
    omega

private def freeArcRowsWithWork {A : Type*} [DecidableEq A] (arcs : Finset A) : List A → List A × ℕ
  | [] => ([],2)
  | key :: rest =>
    let found := memFinsetWithWordWork key arcs
    let tail := freeArcRowsWithWork arcs rest
    (if found.1 then key::tail.1 else tail.1,found.2+tail.2+6)

private theorem freeArcRowsWithWork_spec {A : Type*} [DecidableEq A] (arcs : Finset A) (keys : List A) :
    let out := freeArcRowsWithWork arcs keys
    out.1 = keys.filter (fun e => decide (e ∈ arcs)) ∧ out.2 ≤ 2+keys.length*(12*arcs.card+12) := by
  induction keys with
  | nil => simp [freeArcRowsWithWork]
  | cons key tail ih =>
    obtain ⟨test,fee⟩ := memFinsetWithWordWork_spec key arcs
    obtain ⟨keep,work⟩ := ih
    dsimp only [freeArcRowsWithWork]
    rw [test,keep]
    constructor
    · rw [List.filter_cons]
    · change (memFinsetWithWordWork key arcs).2+(freeArcRowsWithWork arcs tail).2+6 ≤
        2+(tail.length+1)*(12*arcs.card+12)
      rw [Nat.add_mul,Nat.one_mul]
      omega

private def forestWeightedRequestsWithWork (rows : ForestNetworkRows V h) (distinct : rows.vertices.Nodup)
    (free : Arcs (ForestNetworkVertex V h)) : List (V × V) → List (WeightedNetworkRequestRows (ForestNetworkVertex V h)) × ℕ
  | [] => ([],3)
  | d :: tail =>
    let current := forestRequestWithWordWork rows.vertices distinct free d
    let attachments := freeArcRowsWithWork current.1.free rows.keys
    let next := forestWeightedRequestsWithWork rows distinct free tail
    (⟨attachments.1,current.1.source,current.1.sink⟩ :: next.1,current.2+attachments.2+next.2+9)

def forestWeightedRequestsWorkBudget (h vertices keys free requests : ℕ) : ℕ :=
  3+requests*(forestRequestWordBudget h vertices free+2+keys*(12*keys+12)+9)

private theorem forestWeightedRequestsWithWork_spec (G : Arcs V) (rows : ForestNetworkRows V h)
    (distinct : rows.vertices.Nodup) (complete : ∀ v, v ∈ rows.vertices)
    (keys : ∀ e, e ∈ rows.keys) (free : Arcs (ForestNetworkVertex V h)) (freeExact : free = forestNetworkZero G h)
    (D : List (V × V)) :
    let out := forestWeightedRequestsWithWork rows distinct free D
    out.1.map WeightedNetworkRequestRows.reference = D.map (forestNetworkDemand G h) ∧
    (∀ d ∈ out.1, d.free.length ≤ rows.keys.length) ∧
    out.2 ≤ forestWeightedRequestsWorkBudget h rows.vertices.length rows.keys.length free.card D.length := by
  induction D with
  | nil => simp [forestWeightedRequestsWithWork,forestWeightedRequestsWorkBudget]
  | cons d tail ih =>
    let current := forestRequestWithWordWork rows.vertices distinct free d
    let attachments := freeArcRowsWithWork current.1.free rows.keys
    let next := forestWeightedRequestsWithWork rows distinct free tail
    let request : WeightedNetworkRequestRows (ForestNetworkVertex V h) :=
      ⟨attachments.1,current.1.source,current.1.sink⟩
    obtain ⟨demand,currentWork⟩ := forestRequestWithWordWork_spec rows.vertices distinct complete free d
    obtain ⟨retained,attachedWork⟩ := freeArcRowsWithWork_spec current.1.free rows.keys
    obtain ⟨chronology,short,nextWork⟩ := ih
    have cardBound : current.1.free.card ≤ rows.keys.length :=
      (Finset.card_le_card (show current.1.free ⊆ rows.keys.toFinset from
        fun e _ => List.mem_toFinset.mpr (keys e))).trans (List.toFinset_card_le _)
    have attachmentBudget := attachedWork.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left rows.keys.length (by omega : 12*current.1.free.card+12 ≤ 12*rows.keys.length+12)) 2)
    have attachmentsEq : attachments.1.toFinset = current.1.free := by
      change attachments.1 = _ at retained
      rw [retained]
      ext e
      simp [keys e]
    have exactDemand : request.reference = forestNetworkDemand G h d := by
      change current.1 = _ at demand
      change WeightedNetworkDemand.mk attachments.1.toFinset current.1.source current.1.sink = _
      rw [attachmentsEq,demand,freeExact]
      rfl
    change (request :: next.1).map WeightedNetworkRequestRows.reference = _ ∧
      (∀ r ∈ request :: next.1, r.free.length ≤ rows.keys.length) ∧ _
    change next.1.map WeightedNetworkRequestRows.reference = _ at chronology
    refine ⟨by rw [List.map_cons,List.map_cons,exactDemand,chronology],?_,?_⟩
    · intro r inside
      rcases List.mem_cons.mp inside with rfl | on
      · change attachments.1.length ≤ _
        rw [retained]
        exact List.length_filter_le _ _
      · exact short r on
    · let unitFee := forestRequestWordBudget h rows.vertices.length free.card+2+rows.keys.length*(12*rows.keys.length+12)+9
      change current.2 ≤ _ at currentWork
      change attachments.2 ≤ _ at attachmentBudget
      change next.2 ≤ 3+tail.length*unitFee at nextWork
      change current.2+attachments.2+next.2+9 ≤ 3+(tail.length+1)*unitFee
      rw [Nat.add_mul,Nat.one_mul]
      dsimp only [unitFee] at ⊢ nextWork
      omega

/-- Build finite forest labels, exact paid costs and current leaf attachments.
Run the binary weighted cover from zero on the prepared forest classes. -/
def binaryForestFractionalWithWork {n : ℕ} (h : ℕ)
    (paid free : Arcs (ForestNetworkVertex (Fin n) h)) (read : Fin n × Fin n → ℕ × ℕ)
    (D : List (Fin n × Fin n)) :
    (List (BinaryWeightedPairRow (ForestNetworkVertex (Fin n) h)) × List (List (List Bool × List Bool))) × ℕ :=
  let rows := finForestNetworkRowsWithWordWork n h
  let exact := finForestNetworkRowsWithWordWork_spec n h
  let labels := binaryFinForestNetworkLabelsWithWork n h
  let width := bitLengthWithWork n
  let demands := forestWeightedRequestsWithWork rows exact.1 free D
  let out := binaryWeightedNetworkFromZeroWithWork rows.keys (forestPaidCostWithWork paid read)
    labels.read labels.count width.1 demands.1
  (out.1,rows.wordWork+labels.work+width.2+demands.2+out.2+11)

/-- The exact paid and free classes and hop table of the metric forest
produce the reference fractional state and chronological cut history. -/
theorem binaryForestFractionalWithWork_refines {n : ℕ} (G : Arcs (Fin n)) (h : ℕ)
    (paid free : Arcs (ForestNetworkVertex (Fin n) h))
    (paidExact : paid = forestNetworkPriced G (heightForest G h)) (freeExact : free = forestNetworkZero G h)
    (read : Fin n × Fin n → ℕ × ℕ) (readFee : ℕ)
    (readExact : ∀ e, (read e).1 = hops G e.1 e.2) (readWork : ∀ e, (read e).2 ≤ readFee)
    (D : List (Fin n × Fin n)) :
    let rows := finForestNetworkRowsWithWordWork n h
    let labels := binaryFinForestNetworkLabelsWithWork n h
    let code := fun v => (labels.read v).1
    let scale := weightedCoverScale paid (forestNetworkWeight G)
    let fuel := weightedCoverFuel paid (forestNetworkWeight G)
    let total := D.length*fuel
    let out := binaryForestFractionalWithWork h paid free read D
    let ref := forestFractionalRun G h D
    out.1.1.map BinaryWeightedPairRow.arc = rows.keys ∧
    (∀ row ∈ out.1.1, row.Encodes paid (forestNetworkWeight G) ref.1 code n.size (n.size+total*(1+total+1)) ∧
      row.ChargeWidths total (1+total)) ∧
    (∃ cuts : List (List (ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h)),
      out.1.2 = cuts.map (binaryEncodeArcs code) ∧ cuts.map List.toFinset = ref.2) ∧
    out.2 ≤ (finForestNetworkPairKeysWordPolynomial n h+3)+(5*h+7*labels.count+13)+(7*n+3)+
      forestWeightedRequestsWorkBudget h rows.vertices.length rows.keys.length free.card D.length+
      binaryWeightedNetworkFromZeroWorkBudget labels.count paid.card rows.keys.length rows.keys.length labels.width n.size
        (12*paid.card+10*h+8*readFee+53) (heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels.width+23)
        scale fuel D.length+11 := by
  let rows := finForestNetworkRowsWithWordWork n h
  let labels := binaryFinForestNetworkLabelsWithWork n h
  let width := bitLengthWithWork n
  let cost := forestPaidCostWithWork paid read
  let keySpec := finForestNetworkRowsWithWordWork_spec n h
  let demands := forestWeightedRequestsWithWork rows keySpec.1 free D
  obtain ⟨vertexNodup,vertices,_,simple,complete,_,rowWork⟩ := keySpec
  obtain ⟨depth,_,_,injective,readBound,labelWork⟩ := binaryFinForestNetworkLabelsWithWork_spec n h
  obtain ⟨requests,short,requestWork⟩ := forestWeightedRequestsWithWork_spec G rows vertexNodup vertices complete free freeExact D
  have costs (e : ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h) :=
    forestPaidCostWithWork_spec G paid read readFee readExact readWork e
  have positive : ∀ e ∈ paid, 0 < forestNetworkWeight G e := by
    rw [paidExact]
    exact forestNetworkPriced_positive G _
  have fits (e) (present : e ∈ paid) : forestNetworkWeight G e < 2^width.1 := by
    rw [paidExact] at present
    obtain ⟨link, inside,rfl⟩ := Finset.mem_map.mp present
    have length := (hops_spec (heightForest_edge_spec (Finset.mem_filter.mp inside).1).2).1
    change heightForestWeight G link ≤ Fintype.card (Fin n) at length
    rw [Fintype.card_fin] at length
    rw [show width.1 = n.size from (bitLengthWithWork_spec n).1]
    exact length.trans_lt (Nat.lt_size_self n)
  obtain ⟨keysKept,states,history,runWork⟩ := binaryWeightedNetworkFromZeroWithWork_refines rows.keys simple complete
    paid (forestNetworkWeight G) positive cost labels.read width.1 (12*paid.card+10*h+8*readFee+53)
    (heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels.width+23) labels.width rows.keys.length
    (fun e _ => (costs e).1) (fun e _ => (costs e).2)
    (fun v => (readBound v).2) fits injective (fun v => (readBound v).1.le) demands.1 short
  have sameLength : demands.1.length = D.length := by
    have count := congrArg List.length requests
    simpa only [List.length_map] using count
  have correct : weightedNetworkRun paid (forestNetworkWeight G) (demands.1.map WeightedNetworkRequestRows.reference)
      (fun _ => 0) = forestFractionalRun G h D := by
    rw [requests,paidExact]
    rfl
  change labels.count = _ at depth
  let out := binaryWeightedNetworkFromZeroWithWork rows.keys cost labels.read labels.count width.1 demands.1
  have widthEq : width.1 = n.size := (bitLengthWithWork_spec n).1
  rw [← depth] at keysKept states history runWork
  rw [correct,sameLength] at states
  rw [correct] at history
  have runBound : out.2 ≤ binaryWeightedNetworkFromZeroWorkBudget labels.count paid.card rows.keys.length
      rows.keys.length labels.width n.size (12*paid.card+10*h+8*readFee+53)
      (heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels.width+23)
      (weightedCoverScale paid (forestNetworkWeight G)) (weightedCoverFuel paid (forestNetworkWeight G)) D.length := by
    rw [← widthEq,← sameLength]
    exact runWork
  refine ⟨keysKept,?_,history,?_⟩
  · intro row inside
    change row ∈ out.1.1 at inside
    obtain ⟨encoded,widths⟩ := states row inside
    exact ⟨by rw [← widthEq]; exact encoded,widths⟩
  · change rows.wordWork+labels.work+width.2+demands.2+out.2+11 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add rowWork labelWork)
      (bitLengthWork_le n)) requestWork) runBound) 11

end OnlineReachabilityPreservers
