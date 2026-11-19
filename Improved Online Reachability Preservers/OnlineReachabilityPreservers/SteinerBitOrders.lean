import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.SteinerBitReplay

/-! Executable index orders for the graph, height histories, and early seed coordinates. -/

namespace OnlineReachabilityPreservers

private def indexOfOrder (A : Type*) [LinearOrder A] [Fintype A] : A ≃ Fin (Fintype.card A) :=
  (Fintype.orderIsoFinOfCardEq A rfl).symm.toEquiv

/-- Cast the proof of the bound while retaining the same runtime index. -/
@[inline] private def castFinIndex {n m : ℕ} (size : n = m) : Fin n ≃ Fin m where
  toFun i := ⟨i.val, size ▸ i.isLt⟩
  invFun i := ⟨i.val, size.symm ▸ i.isLt⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

@[inline] private def castIndexType {A : Type*} [Fintype A] {n : ℕ} (index : A ≃ Fin n) :
    A ≃ Fin (Fintype.card A) :=
  index.trans (castFinIndex (by simpa using (Fintype.card_congr index).symm))

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Number vertices in their given linear order. -/
def steinerVertexIndex (V : Type*) [LinearOrder V] [Fintype V] : V ≃ Fin (Fintype.card V) :=
  indexOfOrder V

/-- The empty history has its own slot. Every label starts a block of shorter histories. -/
def heightLexBlockCount (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => n * heightLexBlockCount n h + 1

private def heightNodeZero (V : Type*) : HeightNode V 0 ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨[], by simp⟩
  left_inv x := Subtype.ext (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero x.property)).symm
  right_inv _ := Subsingleton.elim _ _

private def heightNodeFirst (V : Type*) (height : ℕ) :
    HeightNode V (height + 1) ≃ Option (V × HeightNode V height) where
  toFun node := match node with
    | ⟨[], _⟩ => none
    | ⟨v :: rest, bound⟩ => some (v, ⟨rest, Nat.le_of_succ_le_succ bound⟩)
  invFun node := match node with
    | none => ⟨[], by simp⟩
    | some (v, rest) => ⟨v :: rest.val, Nat.succ_le_succ rest.property⟩
  left_inv node := by rcases node with ⟨node, _⟩; cases node <;> rfl
  right_inv node := by cases node with
    | none => rfl
    | some pair => rcases pair with ⟨v, rest, bound⟩; rfl

/-- Rank and unrank bounded histories in lexicographic order by descending one block per label. -/
def heightNodeLexIndex {V : Type*} {n : ℕ} (vertices : V ≃ Fin n) :
    (height : ℕ) → HeightNode V height ≃ Fin (heightLexBlockCount n height)
  | 0 => heightNodeZero V
  | h + 1 => (heightNodeFirst V h).trans <| (Equiv.optionCongr <|
      (vertices.prodCongr (heightNodeLexIndex vertices h)).trans finProdFinEquiv).trans
        (finSuccEquiv (n * heightLexBlockCount n h)).symm

private theorem heightNodeLex_nil {V : Type*} {n h : ℕ} (vertices : V ≃ Fin n)
    (bound : ([] : List V).length ≤ h + 1) :
    (heightNodeLexIndex vertices (h+1) ⟨[],bound⟩).val = 0 := by
  rfl

private theorem heightNodeLex_cons {V : Type*} {n h : ℕ} (vertices : V ≃ Fin n)
    (v : V) (rest : List V) (bound : (v :: rest).length ≤ h + 1) :
    (heightNodeLexIndex vertices (h+1) ⟨v::rest,bound⟩).val =
      (vertices v).val * heightLexBlockCount n h +
        (heightNodeLexIndex vertices h ⟨rest, Nat.le_of_succ_le_succ bound⟩).val + 1 := by
  change ((finSuccEquiv _).symm (some (finProdFinEquiv (vertices v,
    heightNodeLexIndex vertices h ⟨rest, Nat.le_of_succ_le_succ bound⟩)))).val = _
  rw [finSuccEquiv_symm_some]
  change _ + _ * _ + 1 = _
  ac_rfl

theorem heightNodeLexIndex_strictMono {V : Type*} [LinearOrder V] {n : ℕ}
    (vertices : V ≃ Fin n) (ordered : StrictMono vertices) (height : ℕ) :
    StrictMono (heightNodeLexIndex vertices height) := by
  induction height with
  | zero =>
    rintro ⟨left, leftBound⟩ ⟨right, rightBound⟩ less
    have emptyLeft := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero leftBound)
    have emptyRight := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero rightBound)
    have impossible : left < right := less
    simp [emptyLeft, emptyRight] at impossible
  | succ h ih =>
    rintro ⟨left, leftBound⟩ ⟨right, rightBound⟩ less
    change List.Lex (· < ·) left right at less
    change (heightNodeLexIndex vertices (h+1) ⟨left,leftBound⟩).val <
      (heightNodeLexIndex vertices (h+1) ⟨right,rightBound⟩).val
    cases less with
    | nil =>
      rw [heightNodeLex_nil, heightNodeLex_cons]
      omega
    | @cons v tailLeft tailRight smaller =>
      rw [heightNodeLex_cons, heightNodeLex_cons]
      have tail := ih (show (⟨tailLeft, Nat.le_of_succ_le_succ leftBound⟩ : HeightNode V h) <
          ⟨tailRight, Nat.le_of_succ_le_succ rightBound⟩ from smaller)
      exact Nat.add_lt_add_right (Nat.add_lt_add_left tail _) _
    | @rel v tailLeft w tailRight smaller =>
      rw [heightNodeLex_cons, heightNodeLex_cons]
      have label : (vertices v).val + 1 ≤ (vertices w).val := ordered smaller
      have block := Nat.mul_le_mul_right (heightLexBlockCount n h) label
      rw [Nat.add_mul, Nat.one_mul] at block
      have inside := (heightNodeLexIndex vertices h ⟨tailLeft, Nat.le_of_succ_le_succ leftBound⟩).isLt
      omega

private theorem finEquiv_eq_of_strictMono {V : Type*} [LinearOrder V] {n : ℕ}
    (first second : V ≃ Fin n) (f : StrictMono first) (s : StrictMono second) : first = second := by
  have inverse (u : V ≃ Fin n) (h : StrictMono u) : StrictMono u.symm := by
    intro a b less
    apply h.lt_iff_lt.mp
    simpa only [u.apply_symm_apply] using less
  apply Equiv.ext
  intro v
  apply le_antisymm
  · have le := (s.comp (inverse first f)).id_le (first v)
    simpa only [id_eq, Function.comp_apply, first.symm_apply_apply] using le
  · have le := (f.comp (inverse second s)).id_le (second v)
    simpa only [id_eq, Function.comp_apply, second.symm_apply_apply] using le

/-- The arithmetic block count is the number of bounded histories. -/
theorem heightLexBlockCount_card (V : Type*) [LinearOrder V] [Fintype V] (h : ℕ) :
    heightLexBlockCount (Fintype.card V) h = Fintype.card (HeightNode V h) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (heightNodeLexIndex (steinerVertexIndex V) h)).symm

/-- The direct arithmetic rank returns the same index as the canonical sorted enumeration. -/
theorem heightNodeLexIndex_eq (V : Type*) [LinearOrder V] [Fintype V] (h : ℕ) :
    (heightNodeLexIndex (steinerVertexIndex V) h).trans (finCongr (heightLexBlockCount_card V h)) =
      steinerVertexIndex (HeightNode V h) := by
  apply finEquiv_eq_of_strictMono
  · exact (Fin.cast_strictMono (heightLexBlockCount_card V h)).comp
      (heightNodeLexIndex_strictMono _ (Fintype.orderIsoFinOfCardEq V rfl).symm.strictMono h)
  · exact (Fintype.orderIsoFinOfCardEq (HeightNode V h) rfl).symm.strictMono

private def enterArcKeys (G : Arcs V) : G ≃ G.map (toLex : (V × V) ≃ V ×ₗ V).toEmbedding :=
  let place : (V × V) ≃ V ×ₗ V := toLex
  { toFun := fun e => ⟨place e.val, Finset.mem_map.mpr ⟨e.val,e.property,rfl⟩⟩
    invFun := fun e => ⟨place.symm e.val, by
      obtain ⟨edge, present, matched⟩ := Finset.mem_map.mp e.property
      change place edge = e.val at matched
      rw [← matched, place.symm_apply_apply]
      exact present⟩
    left_inv := fun edge => Subtype.ext (place.symm_apply_apply edge.val)
    right_inv := fun edge => Subtype.ext (place.apply_symm_apply edge.val) }

/-- Number the present arcs lexicographically. -/
def steinerArcIndex (G : Arcs V) : G ≃ Fin G.card :=
  let place : (V × V) ≃ V ×ₗ V := toLex
  let keys := G.map place.toEmbedding
  (enterArcKeys G).trans (keys.orderIsoOfFin (Finset.card_map place.toEmbedding)).symm.toEquiv

private def steinerCoordinatesWithHistory {historyCount : ℕ} (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (vertices : V ≃ Fin (Fintype.card V))
    (history : HeightNode V height ≃ Fin historyCount) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) :=
  let leg := (finTwoEquiv.symm.prodCongr history).trans finProdFinEquiv
  let test := (Equiv.optionCongr leg).trans (finSuccEquiv _).symm
  let tier := ((Equiv.refl (Fin width)).prodCongr test).trans finProdFinEquiv
  let root := (vertices.prodCongr tier).trans finProdFinEquiv
  let trials := ((Equiv.refl (Fin (earlyTrialCount V height))).prodCongr root).trans finProdFinEquiv
  let convert := (Equiv.refl _).prodCongr ((Equiv.refl V).prodCongr ((castFinIndex width_eq.symm).prodCongr (Equiv.refl _)))
  castIndexType (convert.trans trials)

private theorem steinerCoordinatesWithHistory_cast {historyCount canonicalCount : ℕ}
    (G : Arcs V) (height width : ℕ) (width_eq : width = (forestScale G height).log2+1)
    (vertices : V ≃ Fin (Fintype.card V)) (history : HeightNode V height ≃ Fin historyCount)
    (correct : historyCount = canonicalCount) :
    steinerCoordinatesWithHistory G height width width_eq vertices history =
      steinerCoordinatesWithHistory G height width width_eq vertices (history.trans (finCongr correct)) := by
  subst canonicalCount
  rfl

/-- Use a cached width and vertex enumeration to construct the coordinate order. -/
def steinerEarlyCoordinateIndexAtWidth (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (vertices : V ≃ Fin (Fintype.card V)) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) :=
  steinerCoordinatesWithHistory G height width width_eq vertices (indexOfOrder (HeightNode V height))

/-- Compute the same early coordinate order without listing and sorting all histories. -/
def steinerEarlyCoordinateIndexLex (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (vertices : V ≃ Fin (Fintype.card V)) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) :=
  steinerCoordinatesWithHistory G height width width_eq vertices (heightNodeLexIndex vertices height)

def steinerEarlyCoordinateIndex (G : Arcs V) (height : ℕ) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) :=
  steinerEarlyCoordinateIndexAtWidth G height ((forestScale G height).log2+1) rfl (steinerVertexIndex V)

theorem steinerEarlyCoordinateIndexAtWidth_eq (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) :
    steinerEarlyCoordinateIndexAtWidth G height width width_eq (steinerVertexIndex V) =
      steinerEarlyCoordinateIndex G height := by
  subst width
  rfl

/-- The direct coordinate index agrees with the cached-width sorted index at the canonical vertex order. -/
theorem steinerEarlyCoordinateIndexLex_eq (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) :
    steinerEarlyCoordinateIndexLex G height width width_eq (steinerVertexIndex V) =
      steinerEarlyCoordinateIndexAtWidth G height width width_eq (steinerVertexIndex V) := by
  unfold steinerEarlyCoordinateIndexLex
  rw [steinerCoordinatesWithHistory_cast G height width width_eq _ _ (heightLexBlockCount_card V height),
    heightNodeLexIndex_eq]
  rfl

/-- Run the bit-driven replay with index orders constructed from the input graph. -/
def completeSteinerReplayFromOrderedBits (G : Arcs V) (height : ℕ) (bits : List Bool) (D : List (V × V)) :=
  completeSteinerReplayFromBits G height (steinerEarlyCoordinateIndex G height)
    (steinerVertexIndex V) (steinerArcIndex G) bits D

/-- Sort the finite input once and use an array for inverse lookups. -/
def steinerSortedArrayIndex {A : Type*} [LinearOrder A] (values : Finset A) :
    values ≃ Fin values.card :=
  let rows := values.sort
  let array := rows.toArray
  have len : rows.length = values.card := values.length_sort _
  have index (i : Fin values.card) : i.val < rows.length := len.symm ▸ i.isLt
  have indexArray (i : Fin values.card) : i.val < array.size := by
    simpa only [array, List.size_toArray] using index i
  have inside (x : values) : x.val ∈ rows := (values.mem_sort _).mpr x.property
  { toFun := fun x => ⟨rows.idxOf x.val, len ▸ List.idxOf_lt_length_of_mem (inside x)⟩
    invFun := fun i => ⟨array[i.val]'(indexArray i), (values.mem_sort _).mp (by
      simpa only [array, List.getElem_toArray] using List.getElem_mem (l := rows) (index i))⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (inside x))
    right_inv := by
      intro i
      apply Fin.ext
      simpa only [array, List.getElem_toArray] using (values.sort_nodup _).idxOf_getElem (i := i.val) (index i) }

theorem steinerSortedArrayIndex_eq {A : Type*} [LinearOrder A] (values : Finset A) :
    steinerSortedArrayIndex values = (values.orderIsoOfFin rfl).symm.toEquiv := by
  ext x
  exact (values.orderIsoOfFin_symm_apply rfl x).symm

/-- Construct the ordinary increasing index for a finite type with one sort. -/
def steinerUniverseArrayIndex (A : Type*) [LinearOrder A] [Fintype A] :
    A ≃ Fin (Fintype.card A) :=
  (Equiv.subtypeUnivEquiv (fun a : A => Finset.mem_univ a)).symm.trans
    (steinerSortedArrayIndex (Finset.univ : Finset A))

theorem steinerUniverseArrayIndex_eq (A : Type*) [LinearOrder A] [Fintype A] :
    steinerUniverseArrayIndex A = steinerVertexIndex A := by
  unfold steinerUniverseArrayIndex
  rw [steinerSortedArrayIndex_eq]
  ext a
  rfl

/-- Number graph arcs in their existing lexicographic order using array lookup. -/
def steinerArcArrayIndex {V : Type*} [LinearOrder V] (G : Arcs V) : G ≃ Fin G.card :=
  let place : (V × V) ≃ V ×ₗ V := toLex
  let keys := G.map place.toEmbedding
  (enterArcKeys G).trans ((steinerSortedArrayIndex keys).trans (castFinIndex (Finset.card_map place.toEmbedding)))

theorem steinerArcArrayIndex_eq {V : Type*} [LinearOrder V] [Fintype V] (G : Arcs V) :
    steinerArcArrayIndex G = steinerArcIndex G := by
  ext a
  rfl

end OnlineReachabilityPreservers
