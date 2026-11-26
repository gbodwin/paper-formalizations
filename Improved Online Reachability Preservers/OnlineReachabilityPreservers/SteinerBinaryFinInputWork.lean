import OnlineReachabilityPreservers.SteinerBinaryThinSampleWork

/-! Prepare consistent binary labels and complete pair keys from finite graph inputs. -/

namespace OnlineReachabilityPreservers

/-- The common fixed-width word for a finite vertex label. -/
def binaryFinLabel {n : ℕ} (width : ℕ) (vertex : Fin n) : List Bool :=
  (encodeBoundedNatWithBinaryWork vertex.val width).1

theorem binaryFinLabel_spec {n : ℕ} (width : ℕ) (fits : n ≤ 2^width) (vertex : Fin n) :
    binaryWordValue (binaryFinLabel width vertex) = vertex.val ∧ (binaryFinLabel width vertex).length = width := by
  obtain ⟨value,length,_⟩ := encodeBoundedNatWithBinaryWork_spec vertex.val width (vertex.isLt.trans_le fits)
  exact ⟨value,length⟩

/-- Encode all arc labels in their existing order, for a graph or demand list. -/
def binaryEncodeFinArcsWithWork {n : ℕ} (width : ℕ) : List (Fin n × Fin n) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | arc::rest =>
    let left := encodeBoundedNatWithBinaryWork arc.1.val width
    let right := encodeBoundedNatWithBinaryWork arc.2.val width
    let tail := binaryEncodeFinArcsWithWork width rest
    ((left.1,right.1)::tail.1,left.2+right.2+tail.2+5)

def binaryFinArcEncodingWorkBudget (rows width : ℕ) : ℕ := 2+rows*(2*boundedNatToBinaryWorkBudget width+5)

theorem binaryEncodeFinArcsWithWork_spec {n : ℕ} (width : ℕ) (fits : n ≤ 2^width) (arcs : List (Fin n × Fin n)) :
    let out := binaryEncodeFinArcsWithWork width arcs
    out.1 = binaryEncodeArcs (binaryFinLabel width) arcs ∧ out.2 ≤ binaryFinArcEncodingWorkBudget arcs.length width := by
  induction arcs with
  | nil => simp [binaryEncodeFinArcsWithWork,binaryEncodeArcs,binaryFinArcEncodingWorkBudget]
  | cons arc rest ih =>
    let left := encodeBoundedNatWithBinaryWork arc.1.val width
    let right := encodeBoundedNatWithBinaryWork arc.2.val width
    let tail := binaryEncodeFinArcsWithWork width rest
    obtain ⟨_,_,leftCost⟩ := encodeBoundedNatWithBinaryWork_spec arc.1.val width (arc.1.isLt.trans_le fits)
    obtain ⟨_,_,rightCost⟩ := encodeBoundedNatWithBinaryWork_spec arc.2.val width (arc.2.isLt.trans_le fits)
    obtain ⟨same,cost⟩ := ih
    change tail.1 = _ at same
    change (left.1,right.1)::tail.1 = _ ∧ left.2+right.2+tail.2+5 ≤ binaryFinArcEncodingWorkBudget (rest.length+1) width
    refine ⟨by rw [same]; rfl,?_⟩
    change left.2 ≤ _ at leftCost
    change right.2 ≤ _ at rightCost
    change tail.2 ≤ _ at cost
    unfold binaryFinArcEncodingWorkBudget at cost ⊢
    rw [Nat.add_mul,Nat.one_mul]
    omega

private def binaryEncodeFinVerticesWithWork {n : ℕ} (width : ℕ) : List (Fin n) → List (List Bool) × ℕ
  | [] => ([],2)
  | vertex::rest =>
    let word := encodeBoundedNatWithBinaryWork vertex.val width
    let tail := binaryEncodeFinVerticesWithWork width rest
    (word.1::tail.1,word.2+tail.2+4)

private theorem binaryEncodeFinVerticesWithWork_spec {n : ℕ} (width : ℕ) (fits : n ≤ 2^width)
    (vertices : List (Fin n)) :
    let out := binaryEncodeFinVerticesWithWork width vertices
    out.1 = vertices.map (binaryFinLabel width) ∧
    out.2 ≤ 2+vertices.length*(boundedNatToBinaryWorkBudget width+4) := by
  induction vertices with
  | nil => simp [binaryEncodeFinVerticesWithWork]
  | cons vertex rest ih =>
    let word := encodeBoundedNatWithBinaryWork vertex.val width
    let tail := binaryEncodeFinVerticesWithWork width rest
    obtain ⟨_,_,writeCost⟩ := encodeBoundedNatWithBinaryWork_spec vertex.val width (vertex.isLt.trans_le fits)
    obtain ⟨same,cost⟩ := ih
    change tail.1 = _ at same
    change word.2 ≤ _ at writeCost
    change tail.2 ≤ _ at cost
    change word.1::tail.1 = _ ∧ word.2+tail.2+4 ≤ 2+(rest.length+1)*(boundedNatToBinaryWorkBudget width+4)
    refine ⟨by rw [same]; rfl,?_⟩
    rw [Nat.add_mul,Nat.one_mul]
    omega

private def binaryPairRowWithWork (source : List Bool) : List (List Bool) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | target::rest =>
    let tail := binaryPairRowWithWork source rest
    ((source,target)::tail.1,tail.2+4)

private theorem binaryPairRowWithWork_spec (source : List Bool) (targets : List (List Bool)) :
    binaryPairRowWithWork source targets = (targets.map (Prod.mk source),4*targets.length+2) := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
    simp only [binaryPairRowWithWork,ih,List.map_cons,List.length_cons]
    congr 1

private def binaryPairRowsWithWork (targets : List (List Bool)) : List (List Bool) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | source::rest =>
    let head := binaryPairRowWithWork source targets
    let tail := binaryPairRowsWithWork targets rest
    (head.1++tail.1,2*head.2+tail.2+5)

private theorem binaryPairRowsWithWork_spec (sources targets : List (List Bool)) :
    binaryPairRowsWithWork targets sources = (sources.product targets,2+sources.length*(8*targets.length+9)) := by
  induction sources with
  | nil => simp [binaryPairRowsWithWork,List.product]
  | cons source rest ih =>
    simp only [binaryPairRowsWithWork,binaryPairRowWithWork_spec,ih,List.length_cons]
    congr 1
    rw [Nat.add_mul,Nat.one_mul]
    omega

private theorem binaryEncodeArcs_product {A : Type} (code : A → List Bool) (left right : List A) :
    binaryEncodeArcs code (left.product right) = (left.map code).product (right.map code) := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
    unfold binaryEncodeArcs at ih ⊢
    change List.map (fun arc => (code arc.1,code arc.2)) (right.map (Prod.mk head) ++ rest.product right) =
      (right.map code).map (Prod.mk (code head)) ++ (rest.map code).product (right.map code)
    rw [List.map_append,ih]
    simp only [List.map_map,Function.comp_def]

/-- Encode the vertex list once and enumerate all ordered pairs, including
self-pairs, using those stored words. -/
def binaryCompleteFinKeysWithWork {n : ℕ} (width : ℕ) (vertices : List (Fin n)) : List (List Bool × List Bool) × ℕ :=
  let words := binaryEncodeFinVerticesWithWork width vertices
  let pairs := binaryPairRowsWithWork words.1 words.1
  (pairs.1,words.2+pairs.2+4)

def binaryCompleteFinKeysWorkBudget (vertices width : ℕ) : ℕ :=
  8+vertices*(boundedNatToBinaryWorkBudget width+4)+vertices*(8*vertices+9)

/-- The generated keys are exactly the ordered product of the original
vertex list. A complete vertex list supplies every needed table key. -/
theorem binaryCompleteFinKeysWithWork_spec {n : ℕ} (width : ℕ) (fits : n ≤ 2^width)
    (vertices : List (Fin n)) (complete : ∀ v, v ∈ vertices) :
    let out := binaryCompleteFinKeysWithWork width vertices
    out.1 = binaryEncodeArcs (binaryFinLabel width) (vertices.product vertices) ∧
      (∀ arc : Fin n × Fin n, arc ∈ vertices.product vertices) ∧
      out.2 ≤ binaryCompleteFinKeysWorkBudget vertices.length width := by
  let words := binaryEncodeFinVerticesWithWork width vertices
  obtain ⟨same,cost⟩ := binaryEncodeFinVerticesWithWork_spec width fits vertices
  change words.1 = _ at same
  change words.2 ≤ _ at cost
  have pairs := binaryPairRowsWithWork_spec words.1 words.1
  have size : words.1.length = vertices.length := by simp [same]
  refine ⟨?_,fun e => List.mem_product.mpr ⟨complete e.1,complete e.2⟩,?_⟩
  · change (binaryPairRowsWithWork words.1 words.1).1 = _
    rw [pairs,same,binaryEncodeArcs_product]
  · change words.2+(binaryPairRowsWithWork words.1 words.1).2+4 ≤ _
    rw [pairs]
    dsimp only
    rw [size]
    unfold binaryCompleteFinKeysWorkBudget
    omega

/-- Prepare a common label width, the actual graph and demand encodings,
and the full pair table before running the thin phase. -/
def binaryThinRoundFromFinInputWithWork {n : ℕ} (G : Arcs (Fin n)) (arcs demands : List (Fin n × Fin n))
    (vertices : List (Fin n)) (base ceiling factor : List Bool) (m fuel : ℕ) (hm : m = G.card)
    (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card) : List (List Bool × List Bool) × ℕ :=
  if demands.isEmpty then ([],2) else
    let width := readBinaryWidthAsNatWithWork base
    let graph := binaryEncodeFinArcsWithWork width.1 arcs
    let keys := binaryCompleteFinKeysWithWork width.1 vertices
    let requests := binaryEncodeFinArcsWithWork width.1 demands
    let run := binaryThinRoundFromIndexedSampleWithWork G graph.1 keys.1 base ceiling factor m fuel
      (boundedNatToBinaryWorkBudget width.1) hm index sample (binaryFinLabel width.1) requests.1
    (run.1,width.2+graph.2+keys.2+requests.2+run.2+6)

def binaryThinRoundFromFinInputWorkBudget (n arcs vertices base ceiling factor supply demands : ℕ) : ℕ :=
  binaryWidthAsNatWorkBudget base+binaryFinArcEncodingWorkBudget arcs base+binaryCompleteFinKeysWorkBudget vertices base+
    binaryFinArcEncodingWorkBudget demands base+
    (binaryWidthAsNatWorkBudget ceiling+prepareBinaryThinSampleRowsWorkBudget supply ceiling (boundedNatToBinaryWorkBudget base)+
      binaryThinRoundFromEmptyWorkBudget n arcs (vertices*vertices) supply base base ceiling ceiling factor supply demands+4)+6

/-- No encoded graph, request list, or pair keys need to be supplied to this
entry. A complete vertex list and the given seed index are used throughout. -/
theorem binaryThinRoundFromFinInputWithWork_refines {n : ℕ}
    (arcs demands : List (Fin n × Fin n)) (simple : arcs.Nodup)
    (reachable : ∀ demand ∈ demands, Reach arcs.toFinset demand.1 demand.2)
    (vertices : List (Fin n)) (complete : ∀ v, v ∈ vertices) (base ceiling factor : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (index : arcs.toFinset ≃ Fin arcs.toFinset.card) (sample : Fin arcs.toFinset.card → Fin arcs.toFinset.card) :
    let G := arcs.toFinset
    let fuel := G.card*(G.card.log2+1)+1
    let out := binaryThinRoundFromFinInputWithWork G arcs demands vertices base ceiling factor G.card fuel rfl index sample
    (∃ selected : List (Fin n × Fin n), out.1 = binaryEncodeArcs (binaryFinLabel base.length) selected ∧
      selected.toFinset = thinRoundRun G (binaryWordValue factor) (fun e => sample (index e)) demands) ∧
    out.2 ≤ binaryThinRoundFromFinInputWorkBudget n arcs.length vertices.length base.length ceiling.length factor.length
      G.card demands.length := by
  let G := arcs.toFinset
  let fuel := G.card*(G.card.log2+1)+1
  let width := readBinaryWidthAsNatWithWork base
  let code : Fin n → List Bool := binaryFinLabel base.length
  have fits : n ≤ 2^base.length := (size ▸ binaryWordValue_lt_pow base).le
  have numeric : ∀ v, binaryWordValue (code v) = v.val := fun v => (binaryFinLabel_spec base.length fits v).1
  have bounded : ∀ v, (code v).length ≤ base.length := fun v => (binaryFinLabel_spec base.length fits v).2.le
  obtain ⟨actualWidth,widthCost⟩ := readBinaryWidthAsNatWithWork_spec base
  obtain ⟨graphEq,graphCost⟩ := binaryEncodeFinArcsWithWork_spec base.length fits arcs
  obtain ⟨keysEq,allKeys,keysCost⟩ := binaryCompleteFinKeysWithWork_spec base.length fits vertices complete
  obtain ⟨requestEq,requestCost⟩ := binaryEncodeFinArcsWithWork_spec base.length fits demands
  obtain ⟨result,runCost⟩ := binaryThinRoundFromIndexedSampleWithWork_refines arcs (vertices.product vertices) demands
    simple allKeys reachable code numeric bounded base ceiling factor size supply index sample
    (boundedNatToBinaryWorkBudget base.length)
  have pairCount : (vertices.product vertices).length = vertices.length*vertices.length := List.length_product _ _
  rw [pairCount] at runCost
  cases demands with
  | nil =>
    refine ⟨⟨[],rfl,by simp [thinRoundRun]⟩,?_⟩
    simp [binaryThinRoundFromFinInputWithWork,binaryThinRoundFromFinInputWorkBudget,binaryWidthAsNatWorkBudget]
  | cons first rest =>
    dsimp only [binaryThinRoundFromFinInputWithWork,List.isEmpty_cons,Bool.false_eq_true,ite_false]
    rw [actualWidth]
    let graph := binaryEncodeFinArcsWithWork base.length arcs
    let keys := binaryCompleteFinKeysWithWork base.length vertices
    let requests := binaryEncodeFinArcsWithWork base.length (first::rest)
    let run := binaryThinRoundFromIndexedSampleWithWork G graph.1 keys.1 base ceiling factor G.card fuel
      (boundedNatToBinaryWorkBudget base.length) rfl index sample code requests.1
    change (∃ selected : List (Fin n × Fin n), run.1 = binaryEncodeArcs code selected ∧ _) ∧
      width.2+graph.2+keys.2+requests.2+run.2+6 ≤ _
    change graph.1 = binaryEncodeArcs code arcs at graphEq
    change keys.1 = binaryEncodeArcs code (vertices.product vertices) at keysEq
    change requests.1 = binaryEncodeArcs code (first::rest) at requestEq
    have exactRun : run = binaryThinRoundFromIndexedSampleWithWork G (binaryEncodeArcs code arcs)
        (binaryEncodeArcs code (vertices.product vertices)) base ceiling factor G.card fuel
        (boundedNatToBinaryWorkBudget base.length) rfl index sample code (binaryEncodeArcs code (first::rest)) := by
      dsimp only [run]
      rw [graphEq,keysEq,requestEq]
    rw [exactRun]
    refine ⟨result,?_⟩
    unfold binaryThinRoundFromFinInputWorkBudget
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add widthCost graphCost)
      keysCost) requestCost) runCost) 6

end OnlineReachabilityPreservers
