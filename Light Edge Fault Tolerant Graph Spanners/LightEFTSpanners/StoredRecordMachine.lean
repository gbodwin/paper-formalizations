import LightEFTSpanners.StoredSampleEncoding

/-! Build actual sample records from a stored rational matrix and four stored
edge lists. Each membership scan, cell construction and list reversal executes
one transition at a time in the inherited rational-atom controller model. -/
namespace LightEFTSpanners.StoredRecords
open Controller
abbrev Weights := List (List ℚ)
def rowValues (es : StoredSample.EdgeLists) (i : ℕ) : ℕ → List ℚ → List SampleRecords.Entry :=
  fun j row => List.rec (motive := fun _ => ℕ → List SampleRecords.Entry) (fun _ => [])
    (fun w _ next j => StoredSample.entry (i,j) w es::next (j+1)) row j

theorem rowValues_nil (es : StoredSample.EdgeLists) (i j : ℕ) : rowValues es i j [] = [] := rfl

theorem rowValues_cons (es : StoredSample.EdgeLists) (i j : ℕ) (w : ℚ) (ws : List ℚ) :
    rowValues es i j (w::ws) = StoredSample.entry (i,j) w es::rowValues es i (j+1) ws := rfl

-- Preserve definitional matching of the unchanged list-length and trace proofs.
attribute [reducible] rowValues

def values (es : StoredSample.EdgeLists) : ℕ → Weights → SampleRecords.Records :=
  fun i rows => List.rec (motive := fun _ => ℕ → SampleRecords.Records) (fun _ => [])
    (fun row _ next i => rowValues es i 0 row::next (i+1)) rows i

theorem values_nil (es : StoredSample.EdgeLists) (i : ℕ) : values es i [] = [] := rfl

theorem values_cons (es : StoredSample.EdgeLists) (i : ℕ) (row : List ℚ) (rows : Weights) :
    values es i (row::rows) = rowValues es i 0 row::values es (i+1) rows := rfl

-- Preserve definitional matching in the unchanged length proof.
attribute [reducible] values

def rowSteps (es : StoredSample.EdgeLists) (i : ℕ) : ℕ → List ℚ → ℕ :=
  fun j row => List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1)
    (fun _ _ next j => StoredSample.entrySteps (i,j) es+2+next (j+1)) row j

theorem rowSteps_nil (es : StoredSample.EdgeLists) (i j : ℕ) : rowSteps es i j [] = 1 := rfl

theorem rowSteps_cons (es : StoredSample.EdgeLists) (i j : ℕ) (w : ℚ) (ws : List ℚ) :
    rowSteps es i j (w::ws) = StoredSample.entrySteps (i,j) es+2+rowSteps es i (j+1) ws := rfl

-- Let arithmetic normalization identify the exact unfolded tail count.
attribute [reducible] rowSteps

inductive State where
  | row : ℕ → Weights → SampleRecords.Records → State
  | cell : ℕ → ℕ → List ℚ → List SampleRecords.Entry → Weights → SampleRecords.Records → State
  | entry : ℕ → ℕ → ℚ → List ℚ → List SampleRecords.Entry → Weights → SampleRecords.Records → StoredSample.State → State
  | revRow : ℕ → Weights → SampleRecords.Records → List SampleRecords.Entry → List SampleRecords.Entry → State
  | revMatrix : SampleRecords.Records → SampleRecords.Records → State
  | halt : SampleRecords.Records → State
  deriving DecidableEq, Repr

def transition (es : StoredSample.EdgeLists) : State → Option State
  | .row _ [] out => some (.revMatrix out [])
  | .row i (r::rs) out => some (.cell i 0 r [] rs out)
  | .cell i _ [] acc rs out => some (.revRow i rs out acc [])
  | .cell i j (w::ws) acc rs out => some (.entry i j w ws acc rs out (.seed (.scan (i,j) es.seed)))
  | .entry i j _ ws acc rs out (.halt a) => some (.cell i (j+1) ws (a::acc) rs out)
  | .entry i j w ws acc rs out s =>
    (StoredSample.transition (i,j) w es s).map (State.entry i j w ws acc rs out)
  | .revRow i rs out [] row => some (.row (i+1) rs (row::out))
  | .revRow i rs out (a::as) row => some (.revRow i rs out as (a::row))
  | .revMatrix [] out => some (.halt out)
  | .revMatrix (r::rs) out => some (.revMatrix rs (r::out))
  | .halt _ => none

@[simp] theorem rowValues_length (es : StoredSample.EdgeLists) (i j : ℕ) (r : List ℚ) :
    (rowValues es i j r).length=r.length := by
  induction r generalizing j with
  | nil => rfl
  | cons w ws ih => simp [rowValues,ih]
@[simp] theorem values_length (es : StoredSample.EdgeLists) (i : ℕ) (W : Weights) :
    (values es i W).length=W.length := by
  induction W generalizing i with
  | nil => rfl
  | cons r rs ih => simp [values,ih]

theorem entry_lift (es : StoredSample.EdgeLists) (i j : ℕ) (w : ℚ) (ws : List ℚ)
    (acc : List SampleRecords.Entry) (rs : Weights) (out : SampleRecords.Records)
    {k : ℕ} {s t : StoredSample.State} (h : Trace (StoredSample.transition (i,j) w es) k s t) :
    Trace (transition es) k (.entry i j w ws acc rs out s) (.entry i j w ws acc rs out t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt a => simp [StoredSample.transition] at he
    | seed x => simpa [transition] using congrArg (Option.map (State.entry i j w ws acc rs out)) he
    | selected a x => simpa [transition] using congrArg (Option.map (State.entry i j w ws acc rs out)) he
    | host a b x => simpa [transition] using congrArg (Option.map (State.entry i j w ws acc rs out)) he
    | drawn a b c x => simpa [transition] using congrArg (Option.map (State.entry i j w ws acc rs out)) he

theorem cell_trace (es : StoredSample.EdgeLists) (i j : ℕ) (r : List ℚ)
    (acc : List SampleRecords.Entry) (rs : Weights) (out : SampleRecords.Records) :
    Trace (transition es) (rowSteps es i j r) (.cell i j r acc rs out)
      (.revRow i rs out ((rowValues es i j r).reverse++acc) []) := by
  induction r generalizing j acc with
  | nil => exact Trace.one rfl
  | cons w ws ih =>
    have h0 := Trace.one (show transition es (.cell i j (w::ws) acc rs out)=
      some (.entry i j w ws acc rs out (.seed (.scan (i,j) es.seed))) from rfl)
    have h1 := entry_lift es i j w ws acc rs out (StoredSample.entry_trace (i,j) w es)
    have h2 := Trace.one (show transition es (.entry i j w ws acc rs out (.halt (StoredSample.entry (i,j) w es)))=
      some (.cell i (j+1) ws (StoredSample.entry (i,j) w es::acc) rs out) from rfl)
    have h3 := ih (j+1) (StoredSample.entry (i,j) w es::acc)
    convert h0.trans (h1.trans (h2.trans h3)) using 1 <;>
      simp [rowSteps,rowValues,List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    all_goals omega
end LightEFTSpanners.StoredRecords
