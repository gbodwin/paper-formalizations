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

/-- Number the present arcs lexicographically. -/
def steinerArcIndex (G : Arcs V) : G ≃ Fin G.card :=
  let place : (V × V) ≃ V ×ₗ V := toLex
  let keys := G.map place.toEmbedding
  let enter : G ≃ keys :=
    { toFun := fun e => ⟨place e.val, Finset.mem_map.mpr ⟨e.val,e.property,rfl⟩⟩
      invFun := fun e => ⟨place.symm e.val, by
        obtain ⟨edge, present, matched⟩ := Finset.mem_map.mp e.property
        change place edge = e.val at matched
        rw [← matched, place.symm_apply_apply]
        exact present⟩
      left_inv := fun edge => Subtype.ext (place.symm_apply_apply edge.val)
      right_inv := fun edge => Subtype.ext (place.apply_symm_apply edge.val) }
  enter.trans (keys.orderIsoOfFin (Finset.card_map place.toEmbedding)).symm.toEquiv

def steinerEarlyCoordinateIndex (G : Arcs V) (height : ℕ) :
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)) :=
  let history := indexOfOrder (HeightNode V height)
  let leg := (finTwoEquiv.symm.prodCongr history).trans finProdFinEquiv
  let test := (Equiv.optionCongr leg).trans (finSuccEquiv _).symm
  let tier := ((Equiv.refl (Fin ((forestScale G height).log2+1))).prodCongr test).trans finProdFinEquiv
  let root := ((steinerVertexIndex V).prodCongr tier).trans finProdFinEquiv
  castIndexType (((Equiv.refl (Fin (earlyTrialCount V height))).prodCongr root).trans finProdFinEquiv)

/-- Run the bit-driven replay with index orders constructed from the input graph. -/
def completeSteinerReplayFromOrderedBits (G : Arcs V) (height : ℕ) (bits : List Bool) (D : List (V × V)) :=
  completeSteinerReplayFromBits G height (steinerEarlyCoordinateIndex G height)
    (steinerVertexIndex V) (steinerArcIndex G) bits D

end OnlineReachabilityPreservers
