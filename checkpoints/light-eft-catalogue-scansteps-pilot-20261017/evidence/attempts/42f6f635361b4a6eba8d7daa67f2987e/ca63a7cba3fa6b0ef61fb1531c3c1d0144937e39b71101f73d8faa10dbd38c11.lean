import LightEFTSpanners.StoredVertexPairEncoding

namespace LightEFTSpanners.StoredComponentRecord
open Controller
structure Input where
  id : ℕ
  vertices : List ℕ
  host : StoredHosts.Input
  deriving DecidableEq, Repr
inductive State where
  | pairs : Input → StoredVertexPairs.State → State
  | halt : StoredHostPreparation.Record → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .pairs r (.halt es) => some (.halt ⟨r.id,es,r.host⟩)
  | .pairs r s => (StoredVertexPairs.transition s).map (State.pairs r)
  | .halt _ => none

def result (r : Input) : StoredHostPreparation.Record :=
  ⟨r.id,StoredVertexPairs.pairs r.vertices r.vertices,r.host⟩
def steps (r : Input) : ℕ := StoredVertexPairs.steps r.vertices r.vertices+1

theorem pairs_lift (r : Input) {k : ℕ} {s u : StoredVertexPairs.State}
    (ht : Trace StoredVertexPairs.transition k s u) :
    Trace transition k (.pairs r s) (.pairs r u) := by
  induction ht with
  | refl => exact .refl _
  | @cons k s u z he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt _ => simp [StoredVertexPairs.transition] at he
    | rows _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.pairs r)) he
    | cells _ _ _ _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.pairs r)) he
    | reverse _ _ => simpa only [transition,Option.map_some] using congrArg (Option.map (State.pairs r)) he

theorem record_trace (r : Input) :
    Trace transition (steps r) (.pairs r (.rows r.vertices r.vertices [])) (.halt (result r)) := by
  exact (pairs_lift r (StoredVertexPairs.pairs_trace r.vertices r.vertices)).trans
    (Trace.one rfl)

structure TypedInput (n : ℕ) where
  id : ℕ
  vertices : List (Fin n)
  host : StoredHosts.TypedInput n

def encode {n : ℕ} (r : TypedInput n) : Input :=
  ⟨r.id,r.vertices.map Fin.val,StoredHosts.encode r.host⟩
def typedResult {n : ℕ} (r : TypedInput n) : StoredHostPreparation.TypedRecord n :=
  ⟨r.id,StoredVertexPairs.typedPairs r.vertices r.vertices,r.host⟩

theorem result_encoded {n : ℕ} (r : TypedInput n) :
    result (encode r)=StoredHostPreparation.encode (typedResult r) := by
  simp only [result,encode,typedResult,StoredHostPreparation.encode,StoredVertexPairs.pairs_encoded]
end LightEFTSpanners.StoredComponentRecord
