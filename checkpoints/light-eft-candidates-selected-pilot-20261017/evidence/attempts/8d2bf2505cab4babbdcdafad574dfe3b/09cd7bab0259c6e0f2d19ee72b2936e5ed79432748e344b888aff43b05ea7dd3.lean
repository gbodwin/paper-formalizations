import LightEFTSpanners.StoredCanonicalRoot

namespace LightEFTSpanners.StoredCanonicalEnumeration
open Controller
abbrev Record := ℕ × List ℕ
inductive State where
  | range : ℕ → List ℕ → State
  | roots : List ℕ → List Record → State
  | root : ℕ → List ℕ → List Record → StoredCanonicalRoot.State → State
  | reverse : List Record → List Record → State
  | halt : List Record → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (edges : List StoredEdges.Edge) : State → Option State
  | .range 0 acc => some (.roots acc [])
  | .range (k+1) acc => some (.range k (k::acc))
  | .roots [] acc => some (.reverse acc [])
  | .roots (r::rs) acc => some (.root r rs acc (.component (.matrix (.zero (.row n [])))))
  | .root _ rs acc (.halt none) => some (.roots rs acc)
  | .root r rs acc (.halt (some vs)) => some (.roots rs ((r,vs)::acc))
  | .root r rs acc s => (StoredCanonicalRoot.transition n r edges s).map (State.root r rs acc)
  | .reverse [] out => some (.halt out)
  | .reverse (r::rs) out => some (.reverse rs (r::out))
  | .halt _ => none

theorem range_trace (n : ℕ) (edges : List StoredEdges.Edge) (k : ℕ) (acc : List ℕ) :
    Trace (transition n edges) (k+1) (.range k acc) (.roots (List.range k++acc) []) := by
  induction k generalizing acc with
  | zero => exact Trace.one rfl
  | succ k ih =>
    simpa [List.range_succ,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n edges (.range (k+1) acc)=some (.range k (k::acc)) from rfl) (ih (k::acc))

theorem root_lift (n r : ℕ) (edges : List StoredEdges.Edge) (rs : List ℕ) (acc : List Record)
    {k : ℕ} {s t : StoredCanonicalRoot.State} (h : Trace (StoredCanonicalRoot.transition n r edges) k s t) :
    Trace (transition n edges) k (.root r rs acc s) (.root r rs acc t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s with
    | halt out => simp [StoredCanonicalRoot.transition] at he
    | component s => simpa only [transition,Option.map_some] using congrArg (Option.map (State.root r rs acc)) he
    | minimum vs s => simpa only [transition,Option.map_some] using congrArg (Option.map (State.root r rs acc)) he

def values {n : ℕ} (edges : List (Fin n × Fin n)) (rs : List (Fin n)) : List Record :=
  rs.filterMap fun r => (StoredCanonicalRoot.result edges r).map fun vs => (r.val,vs)

theorem roots_trace {n : ℕ} (edges : List (Fin n × Fin n)) (rs : List (Fin n)) (acc : List Record) :
    ∃ k,k≤rs.length*(StoredCanonicalRoot.bound n edges.length+2)+1 ∧
      Trace (transition n (StoredEdges.encode edges)) k (.roots (rs.map Fin.val) acc)
        (.reverse ((values edges rs).reverse++acc) []) := by
  induction rs generalizing acc with
  | nil => exact ⟨1,by simp,Trace.one rfl⟩
  | cons r rs ih =>
    obtain ⟨k,hk,ht⟩ := StoredCanonicalRoot.root_trace edges r
    have a := Trace.one (show transition n (StoredEdges.encode edges) (.roots ((r::rs).map Fin.val) acc)=
      some (.root r.val (rs.map Fin.val) acc (.component (.matrix (.zero (.row n []))))) from rfl)
    have b := root_lift n r.val (StoredEdges.encode edges) (rs.map Fin.val) acc ht
    cases hr : StoredCanonicalRoot.result edges r with
    | none =>
      obtain ⟨l,hl,hs⟩ := ih acc
      have c := Trace.one (show transition n (StoredEdges.encode edges)
        (.root r.val (rs.map Fin.val) acc (.halt none))=some (.roots (rs.map Fin.val) acc) from rfl)
      rw [hr] at b
      refine ⟨1+k+1+l,?_,?_⟩
      · simp only [List.length_cons,Nat.add_mul];omega
      · simpa [values,hr,Nat.add_assoc] using a.trans (b.trans (c.trans hs))
    | some vs =>
      obtain ⟨l,hl,hs⟩ := ih ((r.val,vs)::acc)
      have c := Trace.one (show transition n (StoredEdges.encode edges)
        (.root r.val (rs.map Fin.val) acc (.halt (some vs)))=some (.roots (rs.map Fin.val) ((r.val,vs)::acc)) from rfl)
      rw [hr] at b
      refine ⟨1+k+1+l,?_,?_⟩
      · simp only [List.length_cons,Nat.add_mul];omega
      · simpa [values,hr,List.reverse_cons,List.append_assoc,Nat.add_assoc] using a.trans (b.trans (c.trans hs))

theorem reverse_trace (n : ℕ) (edges : List StoredEdges.Edge) (rs out : List Record) :
    Trace (transition n edges) (rs.length+1) (.reverse rs out) (.halt (rs.reverse++out)) := by
  induction rs generalizing out with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc] using
      Trace.cons (show transition n edges (.reverse (r::rs) out)=some (.reverse rs (r::out)) from rfl) (ih (r::out))
end LightEFTSpanners.StoredCanonicalEnumeration
