import OnlineReachabilityPreservers.SteinerFiniteIndexPreparationWork
import OnlineReachabilityPreservers.SteinerRoundingWork

/-! Compute one early seed coordinate by its arithmetic slots and history rank. -/

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

private def earlyTestRankWithWordWork (n height histories : ℕ) (label : V → ℕ × ℕ) :
    Option (Bool × HeightNode V height) → ℕ × ℕ
  | none => (0,3)
  | some (side,node) =>
    let rank := heightNodeRankWithWordWork n label height node
    (rank.1+histories*(finTwoEquiv.symm side).val+1,rank.2+10)

/-- Flatten one gate or history-test choice in the ordinary seed order. -/
def steinerEarlyCoordinateRankWithWordWork {G : Arcs V} {height : ℕ}
    (n width : ℕ) (label : V → ℕ × ℕ) (key : EarlySeedCoordinate G height) : ℕ × ℕ :=
  let counts := heightLexBlockCountWithWordWork n height
  let tests := 2*counts.1+1
  let perRoot := width*tests
  let perTrial := n*perRoot
  let root := label key.2.1
  let chosen := earlyTestRankWithWordWork n height counts.1 label key.2.2.2
  (chosen.1+tests*key.2.2.1.val+perRoot*root.1+perTrial*key.1.val,counts.2+root.2+chosen.2+23)

theorem steinerEarlyCoordinateRankWithWordWork_spec (G : Arcs V) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1)
    (vertices : V ≃ Fin (Fintype.card V)) (label : V → ℕ × ℕ)
    (C : ℕ) (exactLabel : ∀ v, (label v).1 = (vertices v).val) (labelWork : ∀ v, (label v).2 ≤ C)
    (key : EarlySeedCoordinate G height) :
    let out := steinerEarlyCoordinateRankWithWordWork (Fintype.card V) width label key
    out.1 = (steinerEarlyCoordinateIndexLex G height width widthEq vertices key).val ∧
      out.2 ≤ 5*height+C+heightNodeIndexWordBudget height C+34 := by
  subst width
  let n := Fintype.card V
  let counts := heightLexBlockCountWithWordWork n height
  obtain ⟨same,countWork⟩ := heightLexBlockCountWithWordWork_spec n height
  rcases key with ⟨trial,root,tier,test⟩
  have rootWork := labelWork root
  have rootIndex := exactLabel root
  cases test with
  | none =>
    constructor
    · dsimp only [steinerEarlyCoordinateRankWithWordWork, earlyTestRankWithWordWork]
      rw [same,rootIndex]
      rfl
    · change counts.2+(label root).2+3+23 ≤ _
      change counts.2 = _ at countWork
      omega
  | some test =>
    rcases test with ⟨side,node⟩
    obtain ⟨index,work⟩ := heightNodeRankWithWordWork_spec vertices label C exactLabel labelWork height node
    constructor
    · dsimp only [steinerEarlyCoordinateRankWithWordWork, earlyTestRankWithWordWork]
      rw [same,rootIndex,index]
      rfl
    · change counts.2+(label root).2+((heightNodeRankWithWordWork n label height node).2+10)+23 ≤ _
      change (heightNodeRankWithWordWork n label height node).2 ≤ _ at work
      change counts.2 = _ at countWork
      omega

/-- The arithmetic slot and its measured work with Fin vertex labels. -/
def finSteinerEarlyCoordinatePositionWithWordWork {n : ℕ} (G : Arcs (Fin n)) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1) (key : EarlySeedCoordinate G height) :
    Fin (Fintype.card (EarlySeedCoordinate G height)) × ℕ :=
  let labels := fun v : Fin n => (v.val,1)
  let out := steinerEarlyCoordinateRankWithWordWork n width labels key
  let ordinary := steinerEarlyCoordinateIndexLex G height width widthEq (finSteinerVertexIndex n)
  have exactRank := (steinerEarlyCoordinateRankWithWordWork_spec G height width widthEq
    (finSteinerVertexIndex n) labels 1 (fun _ => rfl) (fun _ => le_rfl) key).1
  have sameNat : out.1 = (ordinary key).val := by
    simpa only [Fintype.card_fin] using exactRank
  (⟨out.1, sameNat.symm ▸ (ordinary key).isLt⟩,out.2)

theorem finSteinerEarlyCoordinatePositionWithWordWork_spec {n : ℕ}
    (G : Arcs (Fin n)) (height width : ℕ) (widthEq : width = (forestScale G height).log2+1)
    (key : EarlySeedCoordinate G height) :
    let out := finSteinerEarlyCoordinatePositionWithWordWork G height width widthEq key
    out.1 = steinerEarlyCoordinateIndexLex G height width widthEq (finSteinerVertexIndex n) key ∧
      out.2 ≤ 5*height+1+heightNodeIndexWordBudget height 1+34 := by
  obtain ⟨same,work⟩ := steinerEarlyCoordinateRankWithWordWork_spec G height width widthEq
    (finSteinerVertexIndex n) (fun v => (v.val,1)) 1 (fun _ => rfl) (fun _ => le_rfl) key
  dsimp only [finSteinerEarlyCoordinatePositionWithWordWork]
  constructor
  · apply Fin.ext
    simpa only [Fintype.card_fin] using same
  · simpa only [Fintype.card_fin] using work

/-- Use the metered forward rank wherever the decoder reads the seed array. -/
def finSteinerEarlyCoordinateIndexWithWordWork {n : ℕ} (G : Arcs (Fin n)) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) where
  toFun key := (finSteinerEarlyCoordinatePositionWithWordWork G height width widthEq key).1
  invFun i := (steinerEarlyCoordinateIndexLex G height width widthEq (finSteinerVertexIndex n)).symm i
  left_inv key := by
    dsimp only
    rw [(finSteinerEarlyCoordinatePositionWithWordWork_spec G height width widthEq key).1]
    exact Equiv.symm_apply_apply _ _
  right_inv i := by
    dsimp only
    rw [(finSteinerEarlyCoordinatePositionWithWordWork_spec G height width widthEq _).1]
    exact Equiv.apply_symm_apply _ _

theorem finSteinerEarlyCoordinateIndexWithWordWork_eq {n : ℕ} (G : Arcs (Fin n)) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1) :
    finSteinerEarlyCoordinateIndexWithWordWork G height width widthEq =
      steinerEarlyCoordinateIndexLex G height width widthEq (steinerUniverseArrayIndex (Fin n)) := by
  rw [← finSteinerVertexIndex_eq]
  exact Equiv.ext fun key => (finSteinerEarlyCoordinatePositionWithWordWork_spec G height width widthEq key).1

/-- Account for the arithmetic rank and one access to the stored word. -/
def readFinEarlySeedWordWithRankWork {n : ℕ} (G : Arcs (Fin n)) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1) (words : IndexedEarlySeedWords G height)
    (key : EarlySeedCoordinate G height) : Fin (forestSeedSize (forestScale G height)) × ℕ :=
  let rank := finSteinerEarlyCoordinatePositionWithWordWork G height width widthEq key
  (words rank.1,rank.2+1)

def earlySeedArrayReadWordBudget (height : ℕ) : ℕ :=
  5*height+1+heightNodeIndexWordBudget height 1+35

theorem readFinEarlySeedWordWithRankWork_spec {n : ℕ} (G : Arcs (Fin n)) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1) (words : IndexedEarlySeedWords G height)
    (key : EarlySeedCoordinate G height) :
    let out := readFinEarlySeedWordWithRankWork G height width widthEq words key
    out.1 = words (finSteinerEarlyCoordinateIndexWithWordWork G height width widthEq key) ∧
      out.2 ≤ earlySeedArrayReadWordBudget height :=
  ⟨rfl,Nat.add_le_add_right (finSteinerEarlyCoordinatePositionWithWordWork_spec G height width widthEq key).2 1⟩

/-- Read gates and ancestor samples from the same array when rounding uses them. -/
def finEarlySeedTrialsWithRankWork {n : ℕ} (G : Arcs (Fin n)) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1) (words : IndexedEarlySeedWords G height) :
    ForestTrialArrayWithSeedWork (Fin n) height (forestScale G height) (earlyTrialCount (Fin n) height) :=
  let read := readFinEarlySeedWordWithRankWork G height width widthEq words
  fun trial root tier =>
    (read (trial,root,tier,none),fun side node => read (trial,root,tier,some (side,node)))

theorem finEarlySeedTrialsWithRankWork_spec {n : ℕ} (G : Arcs (Fin n)) (height width : ℕ)
    (widthEq : width = (forestScale G height).log2+1) (words : IndexedEarlySeedWords G height) :
    let out := finEarlySeedTrialsWithRankWork G height width widthEq words
    (fun i => forestRoundingSampleValues (forestScale G height) (out i)) =
      (earlySeedCoordinates G height).symm
        (fun c => words (finSteinerEarlyCoordinateIndexWithWordWork G height width widthEq c)) ∧
    ∀ i, forestSampleWorkBound (out i) (earlySeedArrayReadWordBudget height) := by
  have each (key : EarlySeedCoordinate G height) := readFinEarlySeedWordWithRankWork_spec G height width widthEq words key
  exact ⟨rfl,fun i root tier =>
    ⟨(each (i,root,tier,none)).2,fun side node => (each (i,root,tier,some (side,node))).2⟩⟩

end OnlineReachabilityPreservers
