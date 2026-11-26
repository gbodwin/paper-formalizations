import OnlineReachabilityPreservers.SteinerBinaryFinInputWork

/-! Recover the finite thin graph from the binary phase's output rows. -/

namespace OnlineReachabilityPreservers

/-- Decode the word with a supplied allowance for arithmetic at its largest
operand width. The caller verifies the width against the input. -/
def decodeBinaryNatWithWork (width : ℕ) : List Bool → ℕ × ℕ
  | [] => (0,2)
  | bit::rest =>
    let tail := decodeBinaryNatWithWork width rest
    (bit.toNat+2*tail.1,tail.2+2*(width+1)+5)

theorem decodeBinaryNatWithWork_spec (width : ℕ) (word : List Bool) :
    decodeBinaryNatWithWork width word = (binaryWordValue word,2+word.length*(2*(width+1)+5)) := by
  induction word with
  | nil => simp [decodeBinaryNatWithWork,binaryWordValue]
  | cons bit rest ih =>
    simp only [decodeBinaryNatWithWork,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    congr 1
    · cases bit <;> rfl
    · ac_rfl

/-- Read each output label and check both endpoints before forming a
finite arc. An out-of-range endpoint gives no decoded graph. -/
def decodeBinaryFinArcRowsWithWork {n : ℕ} (width : ℕ) :
    List (List Bool × List Bool) → Option (List (Fin n × Fin n)) × ℕ
  | [] => (some [],2)
  | arc::rest =>
    let left := decodeBinaryNatWithWork width arc.1
    let right := decodeBinaryNatWithWork width arc.2
    let checkWork := left.2+right.2+4*(width+1)+7
    if valid : left.1 < n ∧ right.1 < n then
      let tail := decodeBinaryFinArcRowsWithWork width rest
      (tail.1.map (fun rows => (⟨left.1,valid.1⟩,⟨right.1,valid.2⟩)::rows),checkWork+tail.2)
    else (none,checkWork)

def binaryFinArcDecodingWorkBudget (rows width : ℕ) : ℕ :=
  2+rows*(2*(2+width*(2*(width+1)+5))+4*(width+1)+7)

/-- Decoding any list with the common finite labels gives back the arcs
in that list, including their order and multiplicity. -/
theorem decodeBinaryFinArcRowsWithWork_spec {n : ℕ} (width : ℕ) (fits : n ≤ 2^width)
    (arcs : List (Fin n × Fin n)) :
    let out := decodeBinaryFinArcRowsWithWork (n := n) width (binaryEncodeArcs (binaryFinLabel width) arcs)
    out.1 = some arcs ∧ out.2 = binaryFinArcDecodingWorkBudget arcs.length width := by
  induction arcs with
  | nil => simp [decodeBinaryFinArcRowsWithWork,binaryEncodeArcs,binaryFinArcDecodingWorkBudget]
  | cons first rest ih =>
    let left := binaryFinLabel width first.1
    let right := binaryFinLabel width first.2
    obtain ⟨leftVal,leftWidth⟩ := binaryFinLabel_spec width fits first.1
    obtain ⟨rightVal,rightWidth⟩ := binaryFinLabel_spec width fits first.2
    change binaryWordValue left = first.1.val at leftVal
    change binaryWordValue right = first.2.val at rightVal
    change left.length = width at leftWidth
    change right.length = width at rightWidth
    let readLeft := decodeBinaryNatWithWork width left
    let readRight := decodeBinaryNatWithWork width right
    let fee := 2+width*(2*(width+1)+5)
    have leftExact : readLeft = (first.1.val,fee) := by
      dsimp only [readLeft]
      rw [decodeBinaryNatWithWork_spec,leftVal,leftWidth]
    have rightExact : readRight = (first.2.val,fee) := by
      dsimp only [readRight]
      rw [decodeBinaryNatWithWork_spec,rightVal,rightWidth]
    have valid : readLeft.1 < n ∧ readRight.1 < n := by
      rw [leftExact,rightExact]
      exact ⟨first.1.isLt,first.2.isLt⟩
    obtain ⟨same,work⟩ := ih
    change let out := decodeBinaryFinArcRowsWithWork (n := n) width ((left,right)::binaryEncodeArcs (binaryFinLabel width) rest)
      out.1 = some (first::rest) ∧ out.2 = binaryFinArcDecodingWorkBudget (rest.length+1) width
    rw [decodeBinaryFinArcRowsWithWork,dite_eq_left valid]
    dsimp only
    rw [same,work]
    constructor
    · apply congrArg some
      apply congrArg (fun arc => arc::rest)
      exact Prod.ext (Fin.ext (congrArg Prod.fst leftExact)) (Fin.ext (congrArg Prod.fst rightExact))
    · change readLeft.2+readRight.2+4*(width+1)+7+binaryFinArcDecodingWorkBudget rest.length width = _
      rw [leftExact,rightExact]
      unfold binaryFinArcDecodingWorkBudget fee
      rw [Nat.add_mul,Nat.one_mul]
      omega

private def assembleFinArcsWithWork {n : ℕ} (width : ℕ) :
    List (Fin n × Fin n) → Arcs (Fin n) × ℕ × ℕ
  | [] => (∅,0,2)
  | arc::rest =>
    let tail := assembleFinArcsWithWork width rest
    (insert arc tail.1,tail.2.1+1,tail.2.2+(tail.2.1+1)*(4*(width+1)+8))

def finArcAssemblyWorkBudget (rows width : ℕ) : ℕ := 2+rows*rows*(4*(width+1)+8)

private theorem assembleFinArcsWithWork_spec {n : ℕ} (width : ℕ) (arcs : List (Fin n × Fin n)) :
    let out := assembleFinArcsWithWork width arcs
    out.1 = arcs.toFinset ∧ out.2.1 = arcs.length ∧ out.2.2 ≤ finArcAssemblyWorkBudget arcs.length width := by
  induction arcs with
  | nil => simp [assembleFinArcsWithWork,finArcAssemblyWorkBudget]
  | cons first rest ih =>
    let tail := assembleFinArcsWithWork width rest
    let fee := 4*(width+1)+8
    obtain ⟨same,count,cost⟩ := ih
    change tail.1 = _ at same
    change tail.2.1 = _ at count
    change tail.2.2 ≤ _ at cost
    change insert first tail.1 = (first::rest).toFinset ∧ tail.2.1+1 = rest.length+1 ∧
      tail.2.2+(tail.2.1+1)*fee ≤ finArcAssemblyWorkBudget (rest.length+1) width
    rw [same,count,List.toFinset_cons]
    refine ⟨rfl,rfl,?_⟩
    unfold finArcAssemblyWorkBudget at cost ⊢
    have countBounds : rest.length*rest.length+(rest.length+1) ≤ (rest.length+1)*(rest.length+1) := by
      rw [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul]
      omega
    calc
      _ ≤ 2+rest.length*rest.length*fee+(rest.length+1)*fee := Nat.add_le_add_right cost _
      _ = 2+(rest.length*rest.length+(rest.length+1))*fee := by simp only [Nat.add_mul,Nat.add_assoc]
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ countBounds) _

private theorem binaryEncodeFinArcsWithWork_length {n : ℕ} (width : ℕ) (arcs : List (Fin n × Fin n)) :
    (binaryEncodeFinArcsWithWork width arcs).1.length = arcs.length := by
  induction arcs with
  | nil => rfl
  | cons first rest ih => simp [binaryEncodeFinArcsWithWork,ih]

theorem binaryThinRoundFromFinInputWithWork_length_le {n : ℕ} (G : Arcs (Fin n)) (arcs demands : List (Fin n × Fin n))
    (vertices : List (Fin n)) (base ceiling factor : List Bool) (m fuel : ℕ) (hm : m = G.card)
    (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) :
    (binaryThinRoundFromFinInputWithWork G arcs demands vertices base ceiling factor m fuel hm index sample).1.length ≤
      max arcs.length m := by
  unfold binaryThinRoundFromFinInputWithWork
  split
  · exact Nat.zero_le _
  · dsimp only
    rw [← binaryEncodeFinArcsWithWork_length (readBinaryWidthAsNatWithWork base).1 arcs]
    apply binaryThinRoundFromIndexedSampleWithWork_length_le

/-- Return the typed graph of the binary thin phase, for use by the late
preserver's union with hub paths. -/
def binaryThinTypedGraphWithWork {n : ℕ} (G : Arcs (Fin n)) (arcs demands : List (Fin n × Fin n))
    (vertices : List (Fin n)) (base ceiling factor : List Bool) (m fuel : ℕ) (hm : m = G.card)
    (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) : Arcs (Fin n) × ℕ :=
  if demands.isEmpty then (∅,2) else
    let width := readBinaryWidthAsNatWithWork base
    let run := binaryThinRoundFromFinInputWithWork G arcs demands vertices base ceiling factor m fuel hm index sample
    let decoded := decodeBinaryFinArcRowsWithWork (n := n) width.1 run.1
    let typed := assembleFinArcsWithWork width.1 (decoded.1.getD [])
    (typed.1,width.2+run.2+decoded.2+typed.2.2+7)

def binaryThinTypedGraphWorkBudget (n arcs vertices base ceiling factor supply demands : ℕ) : ℕ :=
  binaryWidthAsNatWorkBudget base+binaryThinRoundFromFinInputWorkBudget n arcs vertices base ceiling factor supply demands+
    binaryFinArcDecodingWorkBudget arcs base+finArcAssemblyWorkBudget arcs base+7

theorem binaryThinTypedGraphWithWork_refines {n : ℕ}
    (arcs demands : List (Fin n × Fin n)) (simple : arcs.Nodup)
    (reachable : ∀ demand ∈ demands, Reach arcs.toFinset demand.1 demand.2)
    (vertices : List (Fin n)) (complete : ∀ v, v ∈ vertices) (base ceiling factor : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (index : arcs.toFinset ≃ Fin arcs.toFinset.card) (sample : Fin arcs.toFinset.card → Fin arcs.toFinset.card) :
    let G := arcs.toFinset
    let fuel := G.card*(G.card.log2+1)+1
    let out := binaryThinTypedGraphWithWork G arcs demands vertices base ceiling factor G.card fuel rfl index sample
    out.1 = thinRoundRun G (binaryWordValue factor) (fun e => sample (index e)) demands ∧
    out.2 ≤ binaryThinTypedGraphWorkBudget n arcs.length vertices.length base.length ceiling.length factor.length
      G.card demands.length := by
  let G := arcs.toFinset
  let fuel := G.card*(G.card.log2+1)+1
  let measured := readBinaryWidthAsNatWithWork base
  have fits : n ≤ 2^base.length := (size ▸ binaryWordValue_lt_pow base).le
  obtain ⟨width,widthCost⟩ := readBinaryWidthAsNatWithWork_spec base
  change measured.1 = base.length at width
  change measured.2 ≤ _ at widthCost
  cases demands with
  | nil => simp [binaryThinTypedGraphWithWork,thinRoundRun,binaryThinTypedGraphWorkBudget,binaryWidthAsNatWorkBudget]
  | cons first rest =>
    let demands := first::rest
    let run := binaryThinRoundFromFinInputWithWork G arcs demands vertices base ceiling factor G.card fuel rfl index sample
    let decoded := decodeBinaryFinArcRowsWithWork (n := n) base.length run.1
    obtain ⟨⟨selected,labels,graph⟩,runCost⟩ := binaryThinRoundFromFinInputWithWork_refines arcs demands simple reachable
      vertices complete base ceiling factor size supply index sample
    change run.1 = binaryEncodeArcs (binaryFinLabel base.length) selected at labels
    have outputCount : run.1.length ≤ arcs.length := by
      have bound := binaryThinRoundFromFinInputWithWork_length_le G arcs demands vertices base ceiling factor G.card fuel rfl
        index sample
      have cardBound : G.card ≤ arcs.length := List.toFinset_card_le arcs
      exact bound.trans (max_le le_rfl cardBound)
    have selectedCount : selected.length ≤ arcs.length := by
      simpa only [labels,binaryEncodeArcs,List.length_map] using outputCount
    obtain ⟨reading,decodeCost⟩ := decodeBinaryFinArcRowsWithWork_spec base.length fits selected
    rw [← labels] at reading decodeCost
    change decoded.1 = some selected at reading
    change decoded.2 = _ at decodeCost
    obtain ⟨typed,_,assembleCost⟩ := assembleFinArcsWithWork_spec base.length selected
    have enoughDecode : decoded.2 ≤ binaryFinArcDecodingWorkBudget arcs.length base.length := by
      rw [decodeCost]
      unfold binaryFinArcDecodingWorkBudget
      gcongr
    have enoughAssemble : (assembleFinArcsWithWork base.length selected).2.2 ≤ finArcAssemblyWorkBudget arcs.length base.length := by
      apply assembleCost.trans
      unfold finArcAssemblyWorkBudget
      gcongr
    dsimp only [binaryThinTypedGraphWithWork,List.isEmpty_cons,Bool.false_eq_true,ite_false]
    change (assembleFinArcsWithWork measured.1 ((decodeBinaryFinArcRowsWithWork (n := n) measured.1 run.1).1.getD [])).1 = _ ∧
      measured.2+run.2+(decodeBinaryFinArcRowsWithWork (n := n) measured.1 run.1).2+
        (assembleFinArcsWithWork measured.1 ((decodeBinaryFinArcRowsWithWork (n := n) measured.1 run.1).1.getD [])).2.2+7 ≤ _
    rw [width]
    change (assembleFinArcsWithWork base.length (decoded.1.getD [])).1 = _ ∧
      measured.2+run.2+decoded.2+(assembleFinArcsWithWork base.length (decoded.1.getD [])).2.2+7 ≤ _
    rw [reading,Option.getD_some]
    refine ⟨typed.trans graph,?_⟩
    unfold binaryThinTypedGraphWorkBudget
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add widthCost runCost) enoughDecode) enoughAssemble) 7

end OnlineReachabilityPreservers
