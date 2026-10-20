import LightEFTSpanners.ControllerTrace

/-!
Charged consumption and serialization of finite primitive response tapes.
One response is consumed per occurrence, including repeated keys. Each response
read, record emission and list-reversal cell is an explicit transition. This is
an atom model over supplied keys and ideal primitive responses, not a random-bit
generator, a paid coordinate enumerator, or a physical bit-complexity claim.
-/
namespace LightEFTSpanners.PaidFlagSerialization
open Controller

inductive State (Key : Type*) where
  | collect : List Key → List Bool → List (Key × Bool) → State Key
  | emit : Key → Bool → List Key → List Bool → List (Key × Bool) → State Key
  | reverse : List (Key × Bool) → List (Key × Bool) → State Key
  | halt : List (Key × Bool) → State Key
  deriving DecidableEq, Repr

def transition {Key : Type*} : State Key → Option (State Key)
  | .collect [] [] acc => some (.reverse acc [])
  | .collect (key::keys) (bit::bits) acc => some (.emit key bit keys bits acc)
  | .collect _ _ _ => none
  | .emit key bit keys bits acc => some (.collect keys bits ((key,bit)::acc))
  | .reverse [] acc => some (.halt acc)
  | .reverse (row::rows) acc => some (.reverse rows (row::acc))
  | .halt _ => none

/-- Reject both missing and surplus primitive responses. -/
theorem mismatched_terminal {Key : Type*} (key : Key) (keys : List Key)
    (bit : Bool) (bits : List Bool) (acc : List (Key × Bool)) :
    transition (.collect (key::keys) [] acc) = none ∧
    transition (.collect [] (bit::bits) acc) = none := ⟨rfl,rfl⟩

theorem collect_trace {Key : Type*} (keys : List Key) (bits : List Bool)
    (hlen : bits.length = keys.length) (acc : List (Key × Bool)) :
    Trace transition (2*keys.length+1) (.collect keys bits acc)
      (.reverse ((keys.zip bits).reverse++acc) []) := by
  induction keys generalizing bits acc with
  | nil =>
    cases bits with
    | nil => exact Trace.one rfl
    | cons bit bits => simp at hlen
  | cons key keys ih =>
    cases bits with
    | nil => simp at hlen
    | cons bit bits =>
      have hb : bits.length = keys.length := by simpa using hlen
      have ht := (Trace.one (show transition (.collect (key::keys) (bit::bits) acc) =
        some (.emit key bit keys bits acc) from rfl)).trans
        ((Trace.one (show transition (.emit key bit keys bits acc) =
          some (.collect keys bits ((key,bit)::acc)) from rfl)).trans
          (ih bits hb ((key,bit)::acc)))
      have hcount : 1+(1+(2*keys.length+1)) = 2*(keys.length+1)+1 := by omega
      rw [hcount] at ht
      simpa only [List.length_cons, List.zip_cons_cons, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append] using ht

theorem reverse_trace {Key : Type*} (rows acc : List (Key × Bool)) :
    Trace transition (rows.length+1) (.reverse rows acc) (.halt (rows.reverse++acc)) := by
  induction rows generalizing acc with
  | nil => exact Trace.one rfl
  | cons row rows ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Trace.cons (show transition (.reverse (row::rows) acc) =
        some (.reverse rows (row::acc)) from rfl) (ih (row::acc))

/-- Exact successful transitions, not a padded counter stored in the output. -/
theorem full_trace {Key : Type*} (keys : List Key) (bits : List Bool)
    (hlen : bits.length = keys.length) :
    Trace transition (3*keys.length+2) (.collect keys bits []) (.halt (keys.zip bits)) := by
  have hs := collect_trace keys bits hlen []
  simp only [List.append_nil] at hs
  have hr := reverse_trace (keys.zip bits).reverse []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have hz : (keys.zip bits).length = keys.length := by simp [hlen]
  rw [hz] at hr
  have ht := hs.trans hr
  have hcount : (2*keys.length+1)+(keys.length+1) = 3*keys.length+2 := by omega
  rw [hcount] at ht
  exact ht

def execute {Key : Type*} (keys : List Key) (bits : List Bool) : Option (List (Key × Bool)) :=
  match Controller.run transition (3*keys.length+2) (.collect keys bits []) with
  | .halt rows => some rows
  | _ => none

theorem execute_eq {Key : Type*} (keys : List Key) (bits : List Bool)
    (hlen : bits.length = keys.length) : execute keys bits = some (keys.zip bits) := by
  unfold execute
  rw [(full_trace keys bits hlen).run_eq]

theorem response_count {Key : Type*} (keys : List Key) (bits : List Bool)
    (hlen : bits.length = keys.length) : (keys.zip bits).length = keys.length := by
  simp [hlen]

end LightEFTSpanners.PaidFlagSerialization
