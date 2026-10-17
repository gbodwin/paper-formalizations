import LightEFTSpanners.StoredEdgeMembership
import LightEFTSpanners.SampleRecordMatrix

/-! Construct the four membership fields by executing four real endpoint-list
scans. Only the rational weight cell is supplied; no membership bit is an input. -/
namespace LightEFTSpanners.StoredSample
open Controller
structure EdgeLists where
  seed : List StoredEdges.Edge
  selected : List StoredEdges.Edge
  host : List StoredEdges.Edge
  drawn : List StoredEdges.Edge
  deriving DecidableEq, Repr

def entry (q : StoredEdges.Edge) (w : ℚ) (es : EdgeLists) : SampleRecords.Entry :=
  ⟨w,StoredEdges.contains q es.seed,StoredEdges.contains q es.selected,
    StoredEdges.contains q es.host,StoredEdges.contains q es.drawn⟩
def entrySteps (q : StoredEdges.Edge) (es : EdgeLists) : ℕ :=
  StoredEdges.steps q es.seed+StoredEdges.steps q es.selected+
    StoredEdges.steps q es.host+StoredEdges.steps q es.drawn+4
inductive State where
  | seed : StoredEdges.State → State
  | selected : Bool → StoredEdges.State → State
  | host : Bool → Bool → StoredEdges.State → State
  | drawn : Bool → Bool → Bool → StoredEdges.State → State
  | halt : SampleRecords.Entry → State
  deriving DecidableEq, Repr

def transition (q : StoredEdges.Edge) (w : ℚ) (es : EdgeLists) : State → Option State
  | .seed (.halt b) => some (.selected b (.scan q es.selected))
  | .seed s => (StoredEdges.transition s).map State.seed
  | .selected a (.halt b) => some (.host a b (.scan q es.host))
  | .selected a s => (StoredEdges.transition s).map (State.selected a)
  | .host a b (.halt c) => some (.drawn a b c (.scan q es.drawn))
  | .host a b s => (StoredEdges.transition s).map (State.host a b)
  | .drawn a b c (.halt d) => some (.halt ⟨w,a,b,c,d⟩)
  | .drawn a b c s => (StoredEdges.transition s).map (State.drawn a b c)
  | .halt _ => none

theorem seed_lift (q : StoredEdges.Edge) (w : ℚ) (es : EdgeLists)
    {k : ℕ} {s t : StoredEdges.State} (h : Trace StoredEdges.transition k s t) :
    Trace (transition q w es) k (.seed s) (.seed t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredEdges.transition] at he
    | scan a xs => cases xs <;> simpa [transition] using congrArg (Option.map State.seed) he

theorem selected_lift (q : StoredEdges.Edge) (w : ℚ) (es : EdgeLists) (a : Bool)
    {k : ℕ} {s t : StoredEdges.State} (h : Trace StoredEdges.transition k s t) :
    Trace (transition q w es) k (.selected a s) (.selected a t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt b => simp [StoredEdges.transition] at he
    | scan x xs => cases xs <;> simpa [transition] using congrArg (Option.map (State.selected a)) he

theorem host_lift (q : StoredEdges.Edge) (w : ℚ) (es : EdgeLists) (a b : Bool)
    {k : ℕ} {s t : StoredEdges.State} (h : Trace StoredEdges.transition k s t) :
    Trace (transition q w es) k (.host a b s) (.host a b t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt c => simp [StoredEdges.transition] at he
    | scan x xs => cases xs <;> simpa [transition] using congrArg (Option.map (State.host a b)) he

theorem drawn_lift (q : StoredEdges.Edge) (w : ℚ) (es : EdgeLists) (a b c : Bool)
    {k : ℕ} {s t : StoredEdges.State} (h : Trace StoredEdges.transition k s t) :
    Trace (transition q w es) k (.drawn a b c s) (.drawn a b c t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt d => simp [StoredEdges.transition] at he
    | scan x xs => cases xs <;> simpa [transition] using congrArg (Option.map (State.drawn a b c)) he

theorem entry_trace (q : StoredEdges.Edge) (w : ℚ) (es : EdgeLists) :
    Trace (transition q w es) (entrySteps q es) (.seed (.scan q es.seed)) (.halt (entry q w es)) := by
  have h1 := seed_lift q w es (StoredEdges.scan_trace q es.seed)
  have h2 := selected_lift q w es (StoredEdges.contains q es.seed) (StoredEdges.scan_trace q es.selected)
  have h3 := host_lift q w es (StoredEdges.contains q es.seed) (StoredEdges.contains q es.selected)
    (StoredEdges.scan_trace q es.host)
  have h4 := drawn_lift q w es (StoredEdges.contains q es.seed) (StoredEdges.contains q es.selected)
    (StoredEdges.contains q es.host) (StoredEdges.scan_trace q es.drawn)
  have t1 := Trace.one (show transition q w es (.seed (.halt (StoredEdges.contains q es.seed)))=
    some (.selected (StoredEdges.contains q es.seed) (.scan q es.selected)) from rfl)
  have t2 := Trace.one (show transition q w es (.selected (StoredEdges.contains q es.seed)
      (.halt (StoredEdges.contains q es.selected)))=
    some (.host (StoredEdges.contains q es.seed) (StoredEdges.contains q es.selected) (.scan q es.host)) from rfl)
  have t3 := Trace.one (show transition q w es (.host (StoredEdges.contains q es.seed)
      (StoredEdges.contains q es.selected) (.halt (StoredEdges.contains q es.host)))=
    some (.drawn (StoredEdges.contains q es.seed) (StoredEdges.contains q es.selected)
      (StoredEdges.contains q es.host) (.scan q es.drawn)) from rfl)
  have t4 := Trace.one (show transition q w es (.drawn (StoredEdges.contains q es.seed)
      (StoredEdges.contains q es.selected) (StoredEdges.contains q es.host)
      (.halt (StoredEdges.contains q es.drawn)))=some (.halt (entry q w es)) from rfl)
  have all := h1.trans (t1.trans (h2.trans (t2.trans (h3.trans (t3.trans (h4.trans t4))))))
  convert all using 1
  unfold entrySteps
  omega

theorem entrySteps_le (q : StoredEdges.Edge) (es : EdgeLists) :
    entrySteps q es ≤ es.seed.length+es.selected.length+es.host.length+es.drawn.length+8 := by
  have h1 := StoredEdges.steps_le q es.seed
  have h2 := StoredEdges.steps_le q es.selected
  have h3 := StoredEdges.steps_le q es.host
  have h4 := StoredEdges.steps_le q es.drawn
  unfold entrySteps
  omega
end LightEFTSpanners.StoredSample
