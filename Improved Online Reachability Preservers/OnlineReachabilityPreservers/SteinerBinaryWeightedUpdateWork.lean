import OnlineReachabilityPreservers.SteinerBinaryWeightedCutWork

/-! Apply a paid cut to the represented weighted pair states. -/

namespace OnlineReachabilityPreservers

/-- Separate width allowances for the two words used to advance a charge. -/
def BinaryWeightedPairRow.ChargeWidths {V : Type*} (row : BinaryWeightedPairRow V) (remainder power : ℕ) : Prop :=
  ∀ cost state, row.paid = some (cost,state) → state.remainder.length ≤ remainder ∧ state.power.length ≤ power

/-- Increment each selected paid entry once, using membership in the cut
and keeping the order and labels of the represented pairs. -/
def chargeBinaryWeightedPairRowWithWork {V : Type*} (cut : List (List Bool × List Bool))
    (row : BinaryWeightedPairRow V) : BinaryWeightedPairRow V × ℕ :=
  match row.paid with
  | none => (row,3)
  | some (cost,state) =>
    let inside := binaryArcMemWithWork row.labels cut
    if inside.1 then
      let advanced := chargeBinaryWeightedLoadWithWork cost state
      ({row with paid := some (cost,advanced.1)},inside.2+advanced.2+7)
    else (row,inside.2+5)

def chargeBinaryWeightedPairRowWorkBudget (cut labels cost remainder power amount : ℕ) : ℕ :=
  2+cut*(10*labels+14)+chargeBinaryWeightedLoadWorkBudget cost remainder power amount+7

variable {V : Type*} [LinearOrder V]

omit [LinearOrder V] in
private theorem binaryWeightedPairRow_relax {edges : Arcs V} {weight charges : V × V → ℕ} {code : V → List Bool}
    {cost remainder power amount : ℕ} {row : BinaryWeightedPairRow V}
    (encoded : row.Encodes edges weight charges code cost amount) (widths : row.ChargeWidths remainder power) :
    row.Encodes edges weight charges code cost (amount+power+1) ∧ row.ChargeWidths (remainder+1) (power+1) := by
  obtain ⟨labels,paid,unpaid⟩ := encoded
  refine ⟨⟨labels,?_,unpaid⟩,?_⟩
  · intro inside
    obtain ⟨c,s,shape,cost,same,short,stored⟩ := paid inside
    exact ⟨c,s,shape,cost,same,short,stored.trans (by omega)⟩
  · intro c s shape
    obtain ⟨widthRem,widthPower⟩ := widths c s shape
    exact ⟨widthRem.trans (Nat.le_succ _),widthPower.trans (Nat.le_succ _)⟩

/-- The weighted row keeps its key and represents the next reference
charge state. Repeated occurrences of an arc in the cut count once. -/
theorem chargeBinaryWeightedPairRowWithWork_spec (edges : Arcs V) (weight charges : V × V → ℕ)
    (positive : ∀ e ∈ edges, 0 < weight e) (cut : List (V × V)) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth remainderWidth powerWidth amountWidth : ℕ)
    (bounded : ∀ v, (code v).length ≤ labels) (row : BinaryWeightedPairRow V)
    (encoded : row.Encodes edges weight charges code costWidth amountWidth)
    (widths : row.ChargeWidths remainderWidth powerWidth) :
    let out := chargeBinaryWeightedPairRowWithWork (binaryEncodeArcs code cut) row
    out.1.arc = row.arc ∧ out.1.labels = row.labels ∧
    out.1.Encodes edges weight (chargeWeightedCut cut.toFinset charges) code costWidth (amountWidth+powerWidth+1) ∧
    out.1.ChargeWidths (remainderWidth+1) (powerWidth+1) ∧
    out.2 ≤ chargeBinaryWeightedPairRowWorkBudget cut.length labels costWidth remainderWidth powerWidth amountWidth := by
  let inside := binaryArcMemWithWork row.labels (binaryEncodeArcs code cut)
  let fee := chargeBinaryWeightedPairRowWorkBudget cut.length labels costWidth remainderWidth powerWidth amountWidth
  obtain ⟨test,work⟩ := binaryArcMemWithWork_spec code injective labels bounded row.arc cut
  rw [← encoded.1] at test work
  change inside.1 = decide (row.arc ∈ cut) at test
  change inside.2 ≤ 2+cut.length*(10*labels+14) at work
  obtain ⟨wider,more⟩ := binaryWeightedPairRow_relax encoded widths
  have unchanged (fresh : row.arc ∈ edges → chargeWeightedCut cut.toFinset charges row.arc = charges row.arc) :
      row.Encodes edges weight (chargeWeightedCut cut.toFinset charges) code costWidth (amountWidth+powerWidth+1) := by
    refine ⟨wider.1,?_,wider.2.2⟩
    intro present
    rw [fresh present]
    exact wider.2.1 present
  unfold chargeBinaryWeightedPairRowWithWork
  cases stored : row.paid with
  | none =>
    have absent : row.arc ∉ edges := by
      intro present
      obtain ⟨c,s,shape,_⟩ := encoded.2.1 present
      rw [stored] at shape
      contradiction
    refine ⟨rfl,rfl,unchanged (fun present => (absent present).elim),more,?_⟩
    change 3 ≤ fee
    unfold fee chargeBinaryWeightedPairRowWorkBudget
    omega
  | some pair =>
    obtain ⟨cost,state⟩ := pair
    have present : row.arc ∈ edges := by
      by_contra absent
      have none := encoded.2.2 absent
      rw [stored] at none
      contradiction
    obtain ⟨cost',state',shape,costValue,represented,costFits,amountFits⟩ := encoded.2.1 present
    have same : (cost,state) = (cost',state') := Option.some.inj (stored.symm.trans shape)
    cases same
    dsimp only
    by_cases crosses : row.arc ∈ cut
    · rw [test,decide_eq_true crosses,ite_eq_left (show true = true from rfl)]
      let advanced := chargeBinaryWeightedLoadWithWork cost state
      have costPositive : 0 < binaryWordValue cost := by rw [costValue]; exact positive row.arc present
      have input : state.Encodes (binaryWordValue cost) (charges row.arc) := by rwa [costValue]
      obtain ⟨next,remainder,doubling,numerator,stepWork⟩ := chargeBinaryWeightedLoadWithWork_spec cost (charges row.arc)
        state costPositive input
      obtain ⟨remFits,powFits⟩ := widths cost state stored
      have feeFits : advanced.2 ≤ chargeBinaryWeightedLoadWorkBudget costWidth remainderWidth powerWidth amountWidth := by
        apply stepWork.trans
        unfold chargeBinaryWeightedLoadWorkBudget
        gcongr
      have fresh : chargeWeightedCut cut.toFinset charges row.arc = charges row.arc+1 := by simp [chargeWeightedCut,crosses]
      refine ⟨rfl,rfl,⟨encoded.1,?_,fun absent => (absent present).elim⟩,?_,?_⟩
      · intro _
        refine ⟨cost,advanced.1,rfl,costValue,?_,costFits,numerator.trans ?_⟩
        · rwa [costValue,← fresh] at next
        · gcongr
      · intro c s same
        have pairEq : (cost,advanced.1) = (c,s) := Option.some.inj same
        cases pairEq
        exact ⟨remainder.trans (Nat.add_le_add_right remFits 1),doubling.trans (Nat.add_le_add_right powFits 1)⟩
      · change inside.2+advanced.2+7 ≤ fee
        unfold fee chargeBinaryWeightedPairRowWorkBudget
        omega
    · rw [test,decide_eq_false crosses,ite_eq_right (show ¬ false = true from by decide)]
      have fresh : chargeWeightedCut cut.toFinset charges row.arc = charges row.arc := by simp [chargeWeightedCut,crosses]
      refine ⟨rfl,rfl,unchanged (fun _ => fresh),more,?_⟩
      change inside.2+5 ≤ fee
      unfold fee chargeBinaryWeightedPairRowWorkBudget
      omega

/-- Apply one paid cut across the current pair table. -/
def chargeBinaryWeightedPairRowsWithWork {V : Type*} (cut : List (List Bool × List Bool)) :
    List (BinaryWeightedPairRow V) → List (BinaryWeightedPairRow V) × ℕ
  | [] => ([],2)
  | row::rest =>
    let advanced := chargeBinaryWeightedPairRowWithWork cut row
    let tail := chargeBinaryWeightedPairRowsWithWork cut rest
    (advanced.1::tail.1,advanced.2+tail.2+4)

def chargeBinaryWeightedPairRowsWorkBudget (rows cut labels cost remainder power amount : ℕ) : ℕ :=
  2+rows*(chargeBinaryWeightedPairRowWorkBudget cut labels cost remainder power amount+4)

/-- The table of paid states advances by exactly the reference cut charge
and retains the supplied keys and labels. -/
theorem chargeBinaryWeightedPairRowsWithWork_spec (edges : Arcs V) (weight charges : V × V → ℕ)
    (positive : ∀ e ∈ edges, 0 < weight e) (cut : List (V × V)) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth remainderWidth powerWidth amountWidth : ℕ)
    (bounded : ∀ v, (code v).length ≤ labels) (rows : List (BinaryWeightedPairRow V))
    (encoded : ∀ row ∈ rows, row.Encodes edges weight charges code costWidth amountWidth)
    (widths : ∀ row ∈ rows, row.ChargeWidths remainderWidth powerWidth) :
    let out := chargeBinaryWeightedPairRowsWithWork (binaryEncodeArcs code cut) rows
    out.1.map BinaryWeightedPairRow.arc = rows.map BinaryWeightedPairRow.arc ∧
    out.1.map BinaryWeightedPairRow.labels = rows.map BinaryWeightedPairRow.labels ∧
    (∀ row ∈ out.1, row.Encodes edges weight (chargeWeightedCut cut.toFinset charges) code costWidth (amountWidth+powerWidth+1)) ∧
    (∀ row ∈ out.1, row.ChargeWidths (remainderWidth+1) (powerWidth+1)) ∧
    out.2 ≤ chargeBinaryWeightedPairRowsWorkBudget rows.length cut.length labels costWidth remainderWidth powerWidth amountWidth := by
  induction rows with
  | nil => simp [chargeBinaryWeightedPairRowsWithWork,chargeBinaryWeightedPairRowsWorkBudget]
  | cons row rest ih =>
    let advanced := chargeBinaryWeightedPairRowWithWork (binaryEncodeArcs code cut) row
    let tail := chargeBinaryWeightedPairRowsWithWork (binaryEncodeArcs code cut) rest
    let fee := chargeBinaryWeightedPairRowWorkBudget cut.length labels costWidth remainderWidth powerWidth amountWidth
    obtain ⟨sameKey,sameLabel,current,currentWidths,firstCost⟩ := chargeBinaryWeightedPairRowWithWork_spec edges weight
      charges positive cut code injective labels costWidth remainderWidth powerWidth amountWidth bounded row
      (encoded row List.mem_cons_self) (widths row List.mem_cons_self)
    obtain ⟨tailKeys,tailLabels,tailStates,tailWidths,tailCost⟩ := ih
      (fun r present => encoded r (List.mem_cons_of_mem _ present)) (fun r present => widths r (List.mem_cons_of_mem _ present))
    change advanced.1.arc = row.arc at sameKey
    change advanced.1.labels = row.labels at sameLabel
    change tail.1.map BinaryWeightedPairRow.arc = _ at tailKeys
    change tail.1.map BinaryWeightedPairRow.labels = _ at tailLabels
    change advanced.2 ≤ fee at firstCost
    change tail.2 ≤ 2+rest.length*(fee+4) at tailCost
    refine ⟨?_,?_,?_,?_,?_⟩
    · change advanced.1.arc::tail.1.map BinaryWeightedPairRow.arc = row.arc::rest.map BinaryWeightedPairRow.arc
      rw [sameKey,tailKeys]
    · change advanced.1.labels::tail.1.map BinaryWeightedPairRow.labels = row.labels::rest.map BinaryWeightedPairRow.labels
      rw [sameLabel,tailLabels]
    · intro entry present
      rcases List.mem_cons.mp present with rfl | kept
      · exact current
      · exact tailStates entry kept
    · intro entry present
      rcases List.mem_cons.mp present with rfl | kept
      · exact currentWidths
      · exact tailWidths entry kept
    · change advanced.2+tail.2+4 ≤ 2+(rest.length+1)*(fee+4)
      rw [Nat.add_mul,Nat.one_mul]
      omega

end OnlineReachabilityPreservers
