import Mathlib.Data.Prod.Lex
import OnlineReachabilityPreservers.SteinerBitReplay

/-! Executable index orders for the graph, height histories, and early seed coordinates. -/

namespace OnlineReachabilityPreservers

private def indexOfOrder (A : Type*) [LinearOrder A] [Fintype A] : A ≃ Fin (Fintype.card A) :=
  (Fintype.orderIsoFinOfCardEq A rfl).symm.toEquiv

private def castIndexType {A : Type*} [Fintype A] {n : ℕ} (index : A ≃ Fin n) :
    A ≃ Fin (Fintype.card A) :=
  index.trans (finCongr (by simpa using (Fintype.card_congr index).symm))

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Number vertices in their given linear order. -/
def steinerVertexIndex (V : Type*) [LinearOrder V] [Fintype V] : V ≃ Fin (Fintype.card V) :=
  indexOfOrder V

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

/-- Use a cached width and vertex enumeration to construct the coordinate order. -/
def steinerEarlyCoordinateIndexAtWidth (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) (vertices : V ≃ Fin (Fintype.card V)) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) :=
  let history := indexOfOrder (HeightNode V height)
  let leg := (finTwoEquiv.symm.prodCongr history).trans finProdFinEquiv
  let test := (Equiv.optionCongr leg).trans (finSuccEquiv _).symm
  let tier := ((Equiv.refl (Fin width)).prodCongr test).trans finProdFinEquiv
  let root := (vertices.prodCongr tier).trans finProdFinEquiv
  let trials := ((Equiv.refl (Fin (earlyTrialCount V height))).prodCongr root).trans finProdFinEquiv
  let convert := (Equiv.refl _).prodCongr ((Equiv.refl V).prodCongr ((finCongr width_eq.symm).prodCongr (Equiv.refl _)))
  castIndexType (convert.trans trials)

def steinerEarlyCoordinateIndex (G : Arcs V) (height : ℕ) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) :=
  steinerEarlyCoordinateIndexAtWidth G height ((forestScale G height).log2+1) rfl (steinerVertexIndex V)

theorem steinerEarlyCoordinateIndexAtWidth_eq (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1) :
    steinerEarlyCoordinateIndexAtWidth G height width width_eq (steinerVertexIndex V) =
      steinerEarlyCoordinateIndex G height := by
  subst width
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
  (enterArcKeys G).trans ((steinerSortedArrayIndex keys).trans (finCongr (Finset.card_map place.toEmbedding)))

theorem steinerArcArrayIndex_eq {V : Type*} [LinearOrder V] [Fintype V] (G : Arcs V) :
    steinerArcArrayIndex G = steinerArcIndex G := by
  ext a
  rfl

end OnlineReachabilityPreservers
