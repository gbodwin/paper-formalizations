import LightEFTSpanners.ControllerTrace

/-! Literal short-circuit scans of stored undirected endpoint pairs. Natural
comparisons and one list-cell read are atoms, as in the inherited controller
model. No transition invokes a whole-list membership operation. -/
namespace LightEFTSpanners.StoredEdges
open Controller
abbrev Edge := ℕ × ℕ

def same (q e : Edge) : Bool :=
  decide ((q.1=e.1 ∧ q.2=e.2) ∨ (q.1=e.2 ∧ q.2=e.1))
def contains (q : Edge) : List Edge → Bool
  | [] => false
  | e::es => if same q e then true else contains q es
def steps (q : Edge) : List Edge → ℕ
  | [] => 1
  | e::es => if same q e then 1 else steps q es+1
inductive State where
  | scan : Edge → List Edge → State
  | halt : Bool → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .scan _ [] => some (.halt false)
  | .scan q (e::es) => if same q e then some (.halt true) else some (.scan q es)
  | .halt _ => none

theorem scan_trace (q : Edge) (es : List Edge) :
    Trace transition (steps q es) (.scan q es) (.halt (contains q es)) := by
  induction es with
  | nil => exact Trace.one rfl
  | cons e es ih =>
    cases h : same q e with
    | false => simpa [steps,contains,transition,h] using
        Trace.cons (show transition (.scan q (e::es))=some (.scan q es) by simp [transition,h]) ih
    | true => simpa [steps,contains,h] using
        Trace.one (show transition (.scan q (e::es))=some (.halt true) by simp [transition,h])

theorem steps_le (q : Edge) (es : List Edge) : steps q es ≤ es.length+1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [steps,List.length_cons];split <;> omega

theorem run_scan (q : Edge) (es : List Edge) :
    Controller.run transition (es.length+1) (.scan q es)=.halt (contains q es) := by
  have hb := steps_le q es
  have he : es.length+1=steps q es+(es.length+1-steps q es) := by omega
  rw [he,Controller.run_add,(scan_trace q es).run_eq]
  exact Controller.run_terminal transition (.halt (contains q es)) rfl _

theorem contains_true (q : Edge) (es : List Edge) :
    contains q es=true ↔ ∃ e∈es,same q e=true := by
  induction es with
  | nil => simp [contains]
  | cons e es ih => cases h : same q e <;> simp [contains,h,ih]

def encode {n : ℕ} (es : List (Fin n × Fin n)) : List Edge :=
  es.map fun e => (e.1.val,e.2.val)

theorem same_encode {n : ℕ} (u v a b : Fin n) :
    same (u.val,v.val) (a.val,b.val)=decide (s(u,v)=s(a,b)) := by
  simp [same,Fin.ext_iff]

theorem contains_encode {n : ℕ} (u v : Fin n) (es : List (Fin n × Fin n)) :
    contains (u.val,v.val) (encode es)=true ↔
      s(u,v) ∈ es.map (fun e => s(e.1,e.2)) := by
  rw [contains_true]
  simp only [encode,List.mem_map]
  constructor
  · rintro ⟨e,⟨⟨a,b⟩,h,rfl⟩,he⟩
    have heq : s(u,v)=s(a,b) := of_decide_eq_true (by simpa only [same_encode] using he)
    exact ⟨(a,b),h,heq.symm⟩
  · rintro ⟨⟨a,b⟩,h,he⟩
    refine ⟨(a.val,b.val),⟨(a,b),h,rfl⟩,?_⟩
    rw [same_encode]
    exact decide_eq_true he.symm
end LightEFTSpanners.StoredEdges
