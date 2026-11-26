import OnlineReachabilityPreservers.SteinerBinaryWeightedInitWork
import OnlineReachabilityPreservers.SteinerBinaryWeightedTraceWork

/-! Run the binary weighted solver from the initial paid costs and typed requests. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Read both labels for each typed arc and count the work of the reads. -/
def encodeWeightedArcsWithWork {V : Type*} (readLabel : V → List Bool × ℕ) :
    List (V × V) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | (a,b) :: rest =>
    let left := readLabel a
    let right := readLabel b
    let tail := encodeWeightedArcsWithWork readLabel rest
    ((left.1,right.1)::tail.1,left.2+right.2+tail.2+6)

theorem encodeWeightedArcsWithWork_spec {V : Type*} (readLabel : V → List Bool × ℕ)
    (budget : ℕ) (reads : ∀ v, (readLabel v).2 ≤ budget) (arcs : List (V × V)) :
    let out := encodeWeightedArcsWithWork readLabel arcs
    out.1 = binaryEncodeArcs (fun v => (readLabel v).1) arcs ∧ out.2 ≤ 2+arcs.length*(2*budget+6) := by
  induction arcs with
  | nil => simp [encodeWeightedArcsWithWork,binaryEncodeArcs]
  | cons arc tail ih =>
    obtain ⟨a,b⟩ := arc
    have left := reads a
    have right := reads b
    obtain ⟨same,work⟩ := ih
    refine ⟨congrArg ((_,_)::·) same,?_⟩
    change (readLabel a).2+(readLabel b).2+(encodeWeightedArcsWithWork readLabel tail).2+6 ≤
      2+(tail.length+1)*(2*budget+6)
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Encode each request's own free arcs and its two terminals, using the
same label reader as the initial paid table. -/
def encodeWeightedRequestsWithWork {V : Type*} (readLabel : V → List Bool × ℕ) :
    List (WeightedNetworkRequestRows V) → List BinaryWeightedRequestRows × ℕ
  | [] => ([],2)
  | d :: rest =>
    let free := encodeWeightedArcsWithWork readLabel d.free
    let source := readLabel d.source
    let target := readLabel d.target
    let tail := encodeWeightedRequestsWithWork readLabel rest
    (⟨free.1,source.1,target.1⟩ :: tail.1,free.2+source.2+target.2+tail.2+9)

def binaryWeightedRequestEncodingWorkBudget (requests free labelRead : ℕ) : ℕ :=
  2+requests*(free*(2*labelRead+6)+2*labelRead+11)

theorem encodeWeightedRequestsWithWork_spec {V : Type*} (readLabel : V → List Bool × ℕ)
    (budget : ℕ) (reads : ∀ v, (readLabel v).2 ≤ budget)
    (D : List (WeightedNetworkRequestRows V)) (free : ℕ) (short : ∀ d ∈ D, d.free.length ≤ free) :
    let out := encodeWeightedRequestsWithWork readLabel D
    out.1 = D.map (WeightedNetworkRequestRows.encode (fun v => (readLabel v).1)) ∧
      out.2 ≤ binaryWeightedRequestEncodingWorkBudget D.length free budget := by
  induction D with
  | nil => simp [encodeWeightedRequestsWithWork,binaryWeightedRequestEncodingWorkBudget]
  | cons d tail ih =>
    obtain ⟨same,work⟩ := ih (fun next inside => short next (List.mem_cons_of_mem _ inside))
    obtain ⟨freeExact,freeWork⟩ := encodeWeightedArcsWithWork_spec readLabel budget reads d.free
    have used := freeWork.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (short d List.mem_cons_self)) 2)
    have source := reads d.source
    have target := reads d.target
    change (encodeWeightedRequestsWithWork readLabel tail).2 ≤
      2+tail.length*(free*(2*budget+6)+2*budget+11) at work
    simp only [encodeWeightedRequestsWithWork,WeightedNetworkRequestRows.encode,List.map_cons,List.length_cons]
    refine ⟨by rw [same,freeExact],?_⟩
    unfold binaryWeightedRequestEncodingWorkBudget
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Build the initial table, charge the binary control and request encodings,
and run the weighted cover over the chronological request list. -/
def binaryWeightedNetworkFromZeroWithWork {V : Type*} (keys : List (V × V))
    (readCost : V × V → Option ℕ × ℕ) (readLabel : V → List Bool × ℕ)
    (depth width : ℕ) (D : List (WeightedNetworkRequestRows V)) :
    (List (BinaryWeightedPairRow V) × List (List (List Bool × List Bool))) × ℕ :=
  let start := binaryWeightedInitialTableWithWork readCost readLabel width keys
  let controls := binaryWeightedCoverControlsWithWork start.total
  let requests := encodeWeightedRequestsWithWork readLabel D
  let out := binaryWeightedNetworkTraceWithWork start.paidLabels controls.ceiling depth controls.supply controls.fuel
    requests.1 start.rows
  (out.1,start.work+controls.work+requests.2+out.2+9)

def binaryWeightedNetworkFromZeroWorkBudget (depth edges keys free labels width costRead labelRead scale fuel requests : ℕ) : ℕ :=
  binaryWeightedInitialTableWorkBudget keys width costRead labelRead+
    (7*scale+3+boundedNatToBinaryWorkBudget scale.size+9)+
    binaryWeightedRequestEncodingWorkBudget requests free labelRead+
    binaryWeightedNetworkTraceWorkBudget depth edges keys free labels width 0 1 width scale.size scale fuel requests+9

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- From complete typed keys, the supplied metered readers, and typed request
rows, compute the reference weighted cover from zero charges. -/
theorem binaryWeightedNetworkFromZeroWithWork_refines (keys : List (V × V)) (simple : keys.Nodup)
    (complete : ∀ e, e ∈ keys) (edges : Arcs V) (weight : V × V → ℕ) (positive : ∀ e ∈ edges, 0 < weight e)
    (readCost : V × V → Option ℕ × ℕ) (readLabel : V → List Bool × ℕ) (width costRead labelRead labels free : ℕ)
    (costExact : ∀ e ∈ keys, (readCost e).1 = if e ∈ edges then some (weight e) else none)
    (costWork : ∀ e ∈ keys, (readCost e).2 ≤ costRead) (labelWork : ∀ v, (readLabel v).2 ≤ labelRead)
    (fits : ∀ e ∈ edges, weight e < 2^width) (injective : Function.Injective fun v => (readLabel v).1)
    (bounded : ∀ v, (readLabel v).1.length ≤ labels)
    (D : List (WeightedNetworkRequestRows V)) (short : ∀ d ∈ D, d.free.length ≤ free) :
    let out := binaryWeightedNetworkFromZeroWithWork keys readCost readLabel (Fintype.card V) width D
    let code := fun v => (readLabel v).1
    let ref := weightedNetworkRun edges weight (D.map WeightedNetworkRequestRows.reference) (fun _ => 0)
    let scale := weightedCoverScale edges weight
    let fuel := weightedCoverFuel edges weight
    let total := D.length*fuel
    out.1.1.map BinaryWeightedPairRow.arc = keys ∧
    (∀ row ∈ out.1.1, row.Encodes edges weight ref.1 code width (width+total*(1+total+1)) ∧
      row.ChargeWidths total (1+total)) ∧
    (∃ cuts : List (List (V × V)), out.1.2 = cuts.map (binaryEncodeArcs code) ∧ cuts.map List.toFinset = ref.2) ∧
    out.2 ≤ binaryWeightedNetworkFromZeroWorkBudget (Fintype.card V) edges.card keys.length free labels width
      costRead labelRead scale fuel D.length := by
  let start := binaryWeightedInitialTableWithWork readCost readLabel width keys
  let controls := binaryWeightedCoverControlsWithWork start.total
  let requests := encodeWeightedRequestsWithWork readLabel D
  let code := fun v => (readLabel v).1
  let scale := weightedCoverScale edges weight
  let fuel := weightedCoverFuel edges weight
  obtain ⟨keysEq,_,paidLabels,_,states,startWork⟩ := binaryWeightedInitialTableWithWork_spec keys simple edges weight
    readCost readLabel width costRead labelRead costExact costWork labelWork fits
  obtain ⟨paidSimple,paidEq,paidTotal⟩ := binaryWeightedInitialTableWithWork_complete keys simple complete edges weight
    readCost readLabel width costRead labelRead costExact costWork labelWork fits
  change start.paid.toFinset = edges at paidEq
  change start.total = _ at paidTotal
  obtain ⟨supply,suppliedFuel,ceiling,ceilingWidth,controlWork⟩ := binaryWeightedCoverControlsWithWork_spec start.total
  change controls.supply = max 1 start.total at supply
  change controls.fuel = (max 1 start.total).log2.succ*start.total+1 at suppliedFuel
  change binaryWordValue controls.ceiling = max 1 start.total at ceiling
  change controls.ceiling.length = (max 1 start.total).size at ceilingWidth
  change controls.work ≤ 7*max 1 start.total+3+boundedNatToBinaryWorkBudget (max 1 start.total).size+9 at controlWork
  rw [paidTotal] at supply suppliedFuel ceiling ceilingWidth controlWork
  have exactSupply : controls.supply = weightedCoverScale start.paid.toFinset weight := by rw [paidEq]; exact supply
  have exactFuel : controls.fuel = weightedCoverFuel start.paid.toFinset weight := by rw [paidEq]; exact suppliedFuel
  have ceilingValue : binaryWordValue controls.ceiling = controls.supply := ceiling.trans supply.symm
  have paidPositive : ∀ e ∈ start.paid.toFinset, 0 < weight e := by rw [paidEq]; exact positive
  obtain ⟨requestsEq,requestWork⟩ := encodeWeightedRequestsWithWork_spec readLabel labelRead labelWork D free short
  have represented (row : BinaryWeightedPairRow V) (inside : row ∈ start.rows) :
      row.Encodes start.paid.toFinset weight (fun _ => 0) code width width := by
    rw [paidEq]
    exact (states row inside).1
  have covered (e : V × V) : e ∈ start.rows.map BinaryWeightedPairRow.arc := by rw [keysEq]; exact complete e
  obtain ⟨kept,final,finalWidths,cuts,traceWork⟩ := binaryWeightedNetworkTraceWithWork_refines
    start.paid paidSimple weight (fun _ => 0) paidPositive controls.supply controls.fuel exactSupply exactFuel
    controls.ceiling ceilingValue code injective labels width 0 1 width free bounded start.rows covered represented
    (fun row h => (states row h).2) D short
  let out := binaryWeightedNetworkTraceWithWork start.paidLabels controls.ceiling (Fintype.card V)
    controls.supply controls.fuel requests.1 start.rows
  change start.paidLabels = binaryEncodeArcs code start.paid at paidLabels
  change requests.1 = D.map (WeightedNetworkRequestRows.encode code) at requestsEq
  have call : out = binaryWeightedNetworkTraceWithWork (binaryEncodeArcs code start.paid) controls.ceiling
      (Fintype.card V) controls.supply controls.fuel (D.map (WeightedNetworkRequestRows.encode code)) start.rows := by
    dsimp only [out]
    rw [paidLabels,requestsEq]
  have paidCount : start.paid.length = edges.card := by
    rw [← List.toFinset_card_of_nodup paidSimple,paidEq]
  have keyCount : start.rows.length = keys.length := by
    have count := congrArg List.length keysEq
    simpa only [List.length_map] using count
  change controls.supply = scale at supply
  change controls.fuel = fuel at suppliedFuel
  change controls.ceiling.length = scale.size at ceilingWidth
  change controls.work ≤ 7*scale+3+boundedNatToBinaryWorkBudget scale.size+9 at controlWork
  change start.work ≤ binaryWeightedInitialTableWorkBudget keys.length width costRead labelRead at startWork
  change requests.2 ≤ binaryWeightedRequestEncodingWorkBudget D.length free labelRead at requestWork
  change out.1.1.map BinaryWeightedPairRow.arc = keys ∧ _ ∧ _ ∧ start.work+controls.work+requests.2+out.2+9 ≤ _
  rw [← call] at kept final finalWidths cuts traceWork
  rw [paidEq,suppliedFuel] at final
  rw [suppliedFuel] at finalWidths
  rw [paidEq] at cuts
  rw [paidCount,keyCount,ceilingWidth,supply,suppliedFuel] at traceWork
  refine ⟨kept.trans keysEq,fun row h => ⟨final row h,by simpa only [Nat.zero_add] using finalWidths row h⟩,cuts,?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add startWork controlWork) requestWork) traceWork) 9

end OnlineReachabilityPreservers
