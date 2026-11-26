import OnlineReachabilityPreservers.SteinerBinaryLateWork

/-! Prepare the binary late-phase controls from the graph and threshold counts. -/

namespace OnlineReachabilityPreservers

/-- Count words, the late rounding factor, and the numeric loop fuel used
by the binary thin evaluator. -/
structure BinaryLateControls where
  vertices : List Bool
  arcs : List Bool
  factor : List Bool
  fuel : ℕ

/-- Compute and encode the counts and rounding factor at their actual
binary widths. The width reads and encodings are included in the tally. -/
def prepareBinaryLateControlsWithWork (n m τ : ℕ) : BinaryLateControls × ℕ :=
  let nWidth := bitLengthWithWork n
  let mWidth := bitLengthWithWork m
  let roundFactor := τ+4*max 1 nWidth.1
  let factorWidth := bitLengthWithWork roundFactor
  let nWord := encodeBoundedNatWithBinaryWork n nWidth.1
  let mWord := encodeBoundedNatWithBinaryWork m mWidth.1
  let factorWord := encodeBoundedNatWithBinaryWork roundFactor factorWidth.1
  let fuel := m*max 1 mWidth.1+1
  (⟨nWord.1,mWord.1,factorWord.1,fuel⟩,
    nWidth.2+mWidth.2+factorWidth.2+nWord.2+mWord.2+factorWord.2+19)

def prepareBinaryLateControlsWorkBudget (n m factor : ℕ) : ℕ :=
  (7*n+3)+(7*m+3)+(7*factor+3)+boundedNatToBinaryWorkBudget n.size+
    boundedNatToBinaryWorkBudget m.size+boundedNatToBinaryWorkBudget factor.size+19

/-- The produced binary words and numeric fuel are exactly the two graph
counts and the controls used by reference thin rounding. -/
theorem prepareBinaryLateControlsWithWork_spec (n m τ : ℕ) :
    let factor := thinRoundingFactor n τ
    let out := prepareBinaryLateControlsWithWork n m τ
    binaryWordValue out.1.vertices = n ∧ binaryWordValue out.1.arcs = m ∧ binaryWordValue out.1.factor = factor ∧
    out.1.fuel = m*(m.log2+1)+1 ∧ out.1.vertices.length = n.size ∧ out.1.arcs.length = m.size ∧
    out.1.factor.length = factor.size ∧ out.2 ≤ prepareBinaryLateControlsWorkBudget n m factor := by
  let nWidth := bitLengthWithWork n
  let mWidth := bitLengthWithWork m
  let rawFactor := τ+4*max 1 nWidth.1
  let fWidth := bitLengthWithWork rawFactor
  have nExact : nWidth.1 = n.size := (bitLengthWithWork_spec n).1
  have mExact : mWidth.1 = m.size := (bitLengthWithWork_spec m).1
  have fExact : fWidth.1 = rawFactor.size := (bitLengthWithWork_spec rawFactor).1
  have sameFactor : rawFactor = thinRoundingFactor n τ := by
    dsimp only [rawFactor]
    rw [nExact,max_size_eq_log2_add_one]
    rfl
  have sameFuel : m*max 1 mWidth.1+1 = m*(m.log2+1)+1 := by
    rw [mExact,max_size_eq_log2_add_one]
  have nFits : n < 2^nWidth.1 := by rw [nExact]; exact Nat.size_le.mp le_rfl
  have mFits : m < 2^mWidth.1 := by rw [mExact]; exact Nat.size_le.mp le_rfl
  have fFits : rawFactor < 2^fWidth.1 := by rw [fExact]; exact Nat.size_le.mp le_rfl
  obtain ⟨nv,nl,nc⟩ := encodeBoundedNatWithBinaryWork_spec n nWidth.1 nFits
  obtain ⟨mv,ml,mc⟩ := encodeBoundedNatWithBinaryWork_spec m mWidth.1 mFits
  obtain ⟨fv,fl,fc⟩ := encodeBoundedNatWithBinaryWork_spec rawFactor fWidth.1 fFits
  have nWordCost : (encodeBoundedNatWithBinaryWork n nWidth.1).2 ≤ boundedNatToBinaryWorkBudget n.size := by
    simpa only [nExact] using nc
  have mWordCost : (encodeBoundedNatWithBinaryWork m mWidth.1).2 ≤ boundedNatToBinaryWorkBudget m.size := by
    simpa only [mExact] using mc
  have factorWordCost : (encodeBoundedNatWithBinaryWork rawFactor fWidth.1).2 ≤
      boundedNatToBinaryWorkBudget (thinRoundingFactor n τ).size := by
    simpa only [fExact,sameFactor] using fc
  have nCost : nWidth.2 ≤ 7*n+3 := bitLengthWork_le n
  have mCost : mWidth.2 ≤ 7*m+3 := bitLengthWork_le m
  have factorCost : fWidth.2 ≤ 7*thinRoundingFactor n τ+3 := by rw [← sameFactor]; exact bitLengthWork_le rawFactor
  refine ⟨nv,mv,fv.trans sameFactor,sameFuel,nl.trans nExact,ml.trans mExact,fl.trans (fExact.trans (congrArg Nat.size sameFactor)),?_⟩
  change nWidth.2+mWidth.2+fWidth.2+(encodeBoundedNatWithBinaryWork n nWidth.1).2+
    (encodeBoundedNatWithBinaryWork m mWidth.1).2+(encodeBoundedNatWithBinaryWork rawFactor fWidth.1).2+19 ≤ _
  unfold prepareBinaryLateControlsWorkBudget
  omega

/-- Prepare the controls before entering the exact binary thin evaluator
within the existing late phase. -/
def lateSteinerWithPreparedBinaryControls {n : ℕ} (G : Arcs (Fin n)) (arcs : {r : List (Fin n × Fin n) // r.Nodup})
    (τ m : ℕ) (hm : m = G.card) (vertices : List (Fin n)) (hubs : Finset (Fin n))
    (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) (D : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
  let setup := prepareBinaryLateControlsWithWork n m τ
  let out := lateSteinerWithBinaryThinWork G arcs τ m setup.1.fuel hm vertices hubs setup.1.vertices setup.1.arcs
    setup.1.factor index sample D
  (out.1,setup.2+out.2+4)

/-- The finite late evaluator can build all its own binary sizes and
rounding parameters while returning the exact late graph. -/
theorem lateSteinerWithPreparedBinaryControls_refines {n : ℕ} (arcs : {r : List (Fin n × Fin n) // r.Nodup})
    (early : EarlySteinerRule arcs.val.toFinset) (τ : ℕ) (vertices : List (Fin n))
    (simple : vertices.Nodup) (complete : ∀ v, v ∈ vertices) (hubs : Finset (Fin n))
    (index : arcs.val.toFinset ≃ Fin arcs.val.toFinset.card) (sample : Fin arcs.val.toFinset.card → Fin arcs.val.toFinset.card)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach arcs.val.toFinset d.1 d.2) :
    let G := arcs.val.toFinset
    let factor := thinRoundingFactor n τ
    let out := lateSteinerWithPreparedBinaryControls G arcs τ G.card rfl vertices hubs index sample D
    out.1 = assembledSteiner early 0 τ hubs (fun e => sample (index e)) D ∧
    out.2 ≤ prepareBinaryLateControlsWorkBudget n G.card factor+lateHubRoutingWordBudget n arcs.val.length D.length+
      binaryThinTypedGraphWorkBudget n arcs.val.length vertices.length n.size G.card.size factor.size G.card D.length+4 := by
  let G := arcs.val.toFinset
  let setup := prepareBinaryLateControlsWithWork n G.card τ
  let factor := thinRoundingFactor n τ
  obtain ⟨size,supply,value,fuel,baseWidth,arcWidth,factorWidth,setupCost⟩ := prepareBinaryLateControlsWithWork_spec n G.card τ
  obtain ⟨graph,work⟩ := lateSteinerWithBinaryThinWork_refines arcs early τ vertices simple complete hubs setup.1.vertices
    setup.1.arcs setup.1.factor size supply value index sample D feasible
  let finished := lateSteinerWithBinaryThinWork G arcs τ G.card (G.card*(G.card.log2+1)+1) rfl vertices hubs
    setup.1.vertices setup.1.arcs setup.1.factor index sample D
  change setup.1.fuel = _ at fuel
  change finished.2 ≤ lateHubRoutingWordBudget n arcs.val.length D.length+
    binaryThinTypedGraphWorkBudget n arcs.val.length vertices.length setup.1.vertices.length setup.1.arcs.length
      setup.1.factor.length G.card D.length at work
  rw [baseWidth,arcWidth,factorWidth] at work
  change finished.2 ≤ lateHubRoutingWordBudget n arcs.val.length D.length+
    binaryThinTypedGraphWorkBudget n arcs.val.length vertices.length n.size G.card.size factor.size G.card D.length at work
  dsimp only [lateSteinerWithPreparedBinaryControls]
  rw [fuel]
  refine ⟨graph,?_⟩
  change setup.2 ≤ prepareBinaryLateControlsWorkBudget n G.card factor at setupCost
  change setup.2+finished.2+4 ≤ prepareBinaryLateControlsWorkBudget n G.card factor+
    lateHubRoutingWordBudget n arcs.val.length D.length+
    binaryThinTypedGraphWorkBudget n arcs.val.length vertices.length n.size G.card.size factor.size G.card D.length+4
  omega

end OnlineReachabilityPreservers
