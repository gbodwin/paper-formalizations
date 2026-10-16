import LightEFTSpanners.StoredDrawLookup

namespace LightEFTSpanners.StoredForestDrawAttachment
open Controller
abbrev Record := StoredForestHosts.Record
inductive State where
  | records : List Record → List StoredComponentRecord.Input → State
  | lookup : Record → List Record → List StoredComponentRecord.Input → StoredDrawLookup.State → State
  | reverse : List StoredComponentRecord.Input → List StoredComponentRecord.Input → State
  | halt : List StoredComponentRecord.Input → State
  deriving DecidableEq, Repr

def key (n : ℕ) (r : Record) : ℕ := StoredForestHosts.label n r.1 r.2.1.1

def attached (n : ℕ) (r : Record) (ds : StoredVote.Draws) : StoredComponentRecord.Input :=
  ⟨key n r,r.2.1.2,⟨r.2.2,ds⟩⟩

def transition (n : ℕ) (bank : StoredDrawLookup.Bank) : State → Option State
  | .records [] acc => some (.reverse acc [])
  | .records (r::rs) acc => some (.lookup r rs acc (.scan bank))
  | .lookup r rs acc (.halt ds) => some (.records rs ((attached n r ds)::acc))
  | .lookup r rs acc s => (StoredDrawLookup.transition (key n r) s).map (State.lookup r rs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

def value (n : ℕ) (bank : StoredDrawLookup.Bank) (rs : List Record) : List StoredComponentRecord.Input :=
  rs.map fun r => attached n r (StoredDrawLookup.value (key n r) bank)
def scanSteps (n : ℕ) (bank : StoredDrawLookup.Bank) : List Record → ℕ
  | [] => 1
  | r::rs => StoredDrawLookup.steps (key n r) bank+2+scanSteps n bank rs

theorem lookup_lift (n : ℕ) (bank : StoredDrawLookup.Bank) (r : Record) (rs : List Record)
    (acc : List StoredComponentRecord.Input) {k : ℕ} {s t : StoredDrawLookup.State}
    (h : Trace (StoredDrawLookup.transition (key n r)) k s t) :
    Trace (transition n bank) k (.lookup r rs acc s) (.lookup r rs acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredDrawLookup.transition] at he
    | scan xs => simpa only [transition,Option.map_some] using congrArg (Option.map (State.lookup r rs acc)) he

theorem scan_trace (n : ℕ) (bank : StoredDrawLookup.Bank) (rs : List Record)
    (acc : List StoredComponentRecord.Input) :
    Trace (transition n bank) (scanSteps n bank rs) (.records rs acc)
      (.reverse ((value n bank rs).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    have a := Trace.one (show transition n bank (.records (r::rs) acc)=some (.lookup r rs acc (.scan bank)) from rfl)
    have b := lookup_lift n bank r rs acc (StoredDrawLookup.lookup_trace (key n r) bank)
    have c := Trace.one (show transition n bank (.lookup r rs acc (.halt (StoredDrawLookup.value (key n r) bank)))=
      some (.records rs ((attached n r (StoredDrawLookup.value (key n r) bank))::acc)) from rfl)
    have d := ih ((attached n r (StoredDrawLookup.value (key n r) bank))::acc)
    convert a.trans (b.trans (c.trans d)) using 1 <;>
      simp [scanSteps,value,List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega
end LightEFTSpanners.StoredForestDrawAttachment
