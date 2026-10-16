import LightEFTSpanners.StoredOriginalCandidateRecords

namespace LightEFTSpanners.StoredOriginalCandidateRecords
open Controller

theorem scan_trace (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank)
    (xs : List StoredEdges.Edge) (acc : List StoredForestBank.Input) :
    ∃ k,k≤bound Q bank xs ∧ Trace (transition Q bank) k (.scan xs acc) (.halt ((value Q bank xs).reverse++acc)) := by
  induction xs generalizing acc with
  | nil => exact ⟨1,by simp [bound],Trace.one rfl⟩
  | cons x xs ih =>
    have a := Trace.one (show transition Q bank (.scan (x::xs) acc)=some (.member x xs acc (.scan x Q)) from rfl)
    have b := member_lift Q bank x xs acc (StoredEdges.scan_trace x Q)
    have hmem := StoredEdges.steps_le x Q
    cases hr : StoredEdges.contains x Q with
    | true =>
      obtain ⟨k,hk,ht⟩ := ih acc
      rw [hr] at b
      have c := Trace.one (show transition Q bank (.member x xs acc (.halt true))=some (.scan xs acc) from rfl)
      refine ⟨1+(StoredEdges.steps x Q+(1+k)),?_,?_⟩
      · simp only [bound,List.length_cons,Nat.add_mul] at hk ⊢
        omega
      · simpa [value,hr] using a.trans (b.trans (c.trans ht))
    | false =>
      obtain ⟨k,hk,ht⟩ := ih (⟨x,StoredCandidateDrawLookup.value x bank⟩::acc)
      rw [hr] at b
      have c := Trace.one (show transition Q bank (.member x xs acc (.halt false))=some (.draws x xs acc (.scan bank)) from rfl)
      have d := draws_lift Q bank x xs acc (StoredCandidateDrawLookup.lookup_trace x bank)
      have e := Trace.one (show transition Q bank (.draws x xs acc (.halt (StoredCandidateDrawLookup.value x bank)))=
        some (.scan xs (⟨x,StoredCandidateDrawLookup.value x bank⟩::acc)) from rfl)
      have hdraw := StoredCandidateDrawLookup.steps_le x bank
      refine ⟨1+(StoredEdges.steps x Q+(1+(StoredCandidateDrawLookup.steps x bank+(1+k)))),?_,?_⟩
      · simp only [bound,List.length_cons,Nat.add_mul] at hk ⊢
        omega
      · simpa [value,hr,List.reverse_cons,List.append_assoc] using a.trans (b.trans (c.trans (d.trans (e.trans ht))))

def execute (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) : List StoredForestBank.Input :=
  match Controller.run (transition Q bank) (bound Q bank xs) (.scan xs []) with
  | .halt out => out
  | _ => []

theorem execute_eq (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) :
    execute Q bank xs=(value Q bank xs).reverse := by
  obtain ⟨k,hk,ht⟩ := scan_trace Q bank xs []
  have he : bound Q bank xs=k+(bound Q bank xs-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq]
  simp only [List.append_nil]
  rw [Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredOriginalCandidateRecords
