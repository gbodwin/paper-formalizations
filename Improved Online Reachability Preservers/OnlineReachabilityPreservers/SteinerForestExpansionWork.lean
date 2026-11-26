import OnlineReachabilityPreservers.AssignmentListRouteWork
import OnlineReachabilityPreservers.SteinerEarlyReplay
import OnlineReachabilityPreservers.SteinerForestLabelWork
import OnlineReachabilityPreservers.SteinerPhaseUnionWork

/-! Expand bought forest links using measured labels, original routes, and arc unions. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private theorem routeRows_nodup (arcs : List (V × V)) (s t : V) (n : ℕ) (size : n = Fintype.card V) :
    ((routePathListWithWordWork arcs s t n).1.getD []).Nodup := by
  subst n
  rw [(routePathListWithWordWork_spec arcs s t).1]
  cases route : routePath arcs.toFinset s t with
  | none => simp
  | some rows =>
    change rows.Nodup
    exact List.Nodup.of_map Prod.fst (List.nodup_append.mp (routePath_some route).2).1

/-- Expand one forest link by reading its two labels and selecting its
exact hop-decreasing original route. -/
def expandForestLinkWithWordWork {h : ℕ} (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (e : HeightForestVertex V h × HeightForestVertex V h) : Arcs V × ℕ :=
  let s := forestLabelWithWordWork e.1
  let t := forestLabelWithWordWork e.2
  let route := routePathListWithWordWork arcs s.1 t.1 n
  let rows := route.1.getD []
  let simple := routeRows_nodup arcs s.1 t.1 n size
  (⟨(rows : Multiset (V × V)),simple⟩,s.2+t.2+route.2+12)

def expandForestLinkWordBudget (n m h : ℕ) : ℕ := routePathListWordBudget n m+10*h+30

theorem expandForestLinkWithWordWork_spec {h : ℕ} (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (e : HeightForestVertex V h × HeightForestVertex V h) :
    let out := expandForestLinkWithWordWork arcs n size e
    out.1 = pathArcs (routePath arcs.toFinset (heightForestLabel e.1) (heightForestLabel e.2)) ∧
      out.2 ≤ expandForestLinkWordBudget n arcs.length h := by
  subst n
  let s := forestLabelWithWordWork e.1
  let t := forestLabelWithWordWork e.2
  let route := routePathListWithWordWork arcs s.1 t.1 (Fintype.card V)
  obtain ⟨source, sourceCost⟩ := forestLabelWithWordWork_spec e.1
  obtain ⟨target, targetCost⟩ := forestLabelWithWordWork_spec e.2
  obtain ⟨pathEq, routeCost⟩ := routePathListWithWordWork_spec arcs s.1 t.1
  have correct : route.1 = routePath arcs.toFinset (heightForestLabel e.1) (heightForestLabel e.2) := by
    change s.1 = _ at source
    change t.1 = _ at target
    exact pathEq.trans (by rw [source,target])
  refine ⟨?_,?_⟩
  · ext edge
    change edge ∈ route.1.getD [] ↔ edge ∈ _
    rw [correct,pathArcs,List.mem_toFinset]
  · change s.2+t.2+route.2+12 ≤ _
    change route.2 ≤ _ at routeCost
    change s.2 ≤ _ at sourceCost
    change t.2 ≤ _ at targetCost
    unfold expandForestLinkWordBudget
    omega

/-- Scan the available forest links, expand exactly the bought links, and
merge their original paths with metered finite-set unions. -/
def expandForestLinksFromRowsWithWordWork {h : ℕ} (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (bought : Arcs (HeightForestVertex V h)) :
    List (HeightForestVertex V h × HeightForestVertex V h) → Arcs V × ℕ
  | [] => (∅,3)
  | e :: rest =>
    let later := expandForestLinksFromRowsWithWordWork arcs n size bought rest
    let present := memFinsetWithWordWork e bought
    if present.1 then
      let here := expandForestLinkWithWordWork arcs n size e
      let merged := unionFinsetWithWordWork later.1 here.1
      (merged.1,later.2+present.2+here.2+merged.2+11)
    else (later.1,later.2+present.2+6)

def expandForestLinksFromRowsWordBudget (n m h bought rows : ℕ) : ℕ :=
  rows*(12*bought+6+expandForestLinkWordBudget n m h+steinerPhaseUnionWordBudget n+11)+3

theorem expandForestLinksFromRowsWordBudget_le {n m m' h b b' r r' : ℕ}
    (arcs : m ≤ m') (bought : b ≤ b') (rows : r ≤ r') :
    expandForestLinksFromRowsWordBudget n m h b r ≤ expandForestLinksFromRowsWordBudget n m' h b' r' := by
  have route := routePathListWordBudget_mono_arcs n arcs
  unfold expandForestLinksFromRowsWordBudget expandForestLinkWordBudget
  gcongr

private theorem inter_insert_of_member {A : Type*} [DecidableEq A] (selected tail : Finset A) (e : A)
    (member : e ∈ selected) : selected ∩ insert e tail = insert e (selected ∩ tail) := by
  ext key
  simp only [mem_inter,mem_insert]
  constructor
  · rintro ⟨chosen,rfl | later⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨chosen,later⟩
  · rintro (rfl | ⟨chosen,later⟩)
    · exact ⟨member,Or.inl rfl⟩
    · exact ⟨chosen,Or.inr later⟩

private theorem inter_insert_of_absent {A : Type*} [DecidableEq A] (selected tail : Finset A) (e : A)
    (absent : e ∉ selected) : selected ∩ insert e tail = selected ∩ tail := by
  ext key
  simp only [mem_inter,mem_insert]
  constructor
  · rintro ⟨chosen,rfl | later⟩
    · exact (absent chosen).elim
    · exact ⟨chosen,later⟩
  · exact fun ⟨chosen,later⟩ => ⟨chosen,Or.inr later⟩

set_option maxHeartbeats 800000 in
theorem expandForestLinksFromRowsWithWordWork_spec {h : ℕ} (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (bought : Arcs (HeightForestVertex V h)) (rows : List (HeightForestVertex V h × HeightForestVertex V h)) :
    let out := expandForestLinksFromRowsWithWordWork arcs n size bought rows
    out.1 = expandLabelledLinks arcs.toFinset heightForestLabel (bought ∩ rows.toFinset) ∧
      out.2 ≤ expandForestLinksFromRowsWordBudget n arcs.length h bought.card rows.length := by
  let K := 12*bought.card+6+expandForestLinkWordBudget n arcs.length h+steinerPhaseUnionWordBudget n+11
  induction rows with
  | nil =>
    let empty : List (HeightForestVertex V h × HeightForestVertex V h) := []
    change (∅ : Arcs V) = expandLabelledLinks arcs.toFinset heightForestLabel (bought ∩ empty.toFinset) ∧
      3 ≤ expandForestLinksFromRowsWordBudget n arcs.length h bought.card 0
    refine ⟨?_,?_⟩
    · simp only [empty,List.toFinset_nil,inter_empty,expandLabelledLinks]
      ext a
      simp only [Finset.mem_biUnion,Finset.notMem_empty,false_and,exists_false]
    · unfold expandForestLinksFromRowsWordBudget
      rw [Nat.zero_mul,Nat.zero_add]
  | cons e rest ih =>
    let later := expandForestLinksFromRowsWithWordWork arcs n size bought rest
    let present := memFinsetWithWordWork e bought
    obtain ⟨laterEq,laterCost⟩ := ih
    obtain ⟨hit,scan⟩ := memFinsetWithWordWork_spec e bought
    change present.1 = _ at hit
    have budget : expandForestLinksFromRowsWordBudget n arcs.length h bought.card (e :: rest).length =
        rest.length*K+K+3 := by
      simp only [expandForestLinksFromRowsWordBudget,List.length_cons,Nat.succ_mul,K]
    change present.2 ≤ _ at scan
    change later.2 ≤ rest.length*K+3 at laterCost
    by_cases selected : e ∈ bought
    · let here := expandForestLinkWithWordWork arcs n size e
      let merged := unionFinsetWithWordWork later.1 here.1
      obtain ⟨hereEq,hereCost⟩ := expandForestLinkWithWordWork_spec arcs n size e
      have mergedEq := (unionFinsetWithWordWork_spec later.1 here.1).1
      have mergedCost := steinerPhaseUnionWordBudget_bound later.1 here.1
      rw [← size] at mergedCost
      have found : present.1 = true := hit.trans (decide_eq_true selected)
      have output : expandForestLinksFromRowsWithWordWork arcs n size bought (e :: rest) =
          (merged.1,later.2+present.2+here.2+merged.2+11) := by
        change (if present.1 then (merged.1,later.2+present.2+here.2+merged.2+11)
          else (later.1,later.2+present.2+6)) = _
        rw [found]
        rfl
      dsimp only
      rw [output,budget]
      refine ⟨?_,?_⟩
      · change merged.1 = _
        change merged.1 = _ at mergedEq
        rw [mergedEq]
        change later.1 ∪ here.1 = _
        rw [show later.1 = _ from laterEq,show here.1 = _ from hereEq,List.toFinset_cons,
          inter_insert_of_member _ _ _ selected]
        simp only [expandLabelledLinks,Finset.biUnion_insert]
        exact union_comm _ _
      · change later.2+present.2+here.2+merged.2+11 ≤ _
        change here.2 ≤ _ at hereCost
        change merged.2 ≤ _ at mergedCost
        dsimp only [K]
        dsimp only [K] at laterCost
        omega
    · have found : present.1 = false := hit.trans (decide_eq_false selected)
      have output : expandForestLinksFromRowsWithWordWork arcs n size bought (e :: rest) =
          (later.1,later.2+present.2+6) := by
        change (if present.1 then
          (let here := expandForestLinkWithWordWork arcs n size e
           let merged := unionFinsetWithWordWork later.1 here.1
           (merged.1,later.2+present.2+here.2+merged.2+11)) else (later.1,later.2+present.2+6)) = _
        rw [found]
        rfl
      dsimp only
      rw [output,budget]
      refine ⟨?_,?_⟩
      · rw [List.toFinset_cons,inter_insert_of_absent _ _ _ selected]
        exact laterEq
      · change later.2+present.2+6 ≤ _
        dsimp only [K]
        dsimp only [K] at laterCost
        omega

/-- If the supplied template rows contain the bought graph, the expansion
and work bound apply to the whole purchased graph. -/
theorem expandForestLinksFromRowsWithWordWork_complete {h : ℕ} (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (bought : Arcs (HeightForestVertex V h)) (rows : List (HeightForestVertex V h × HeightForestVertex V h))
    (complete : bought ⊆ rows.toFinset) :
    let out := expandForestLinksFromRowsWithWordWork arcs n size bought rows
    out.1 = expandLabelledLinks arcs.toFinset heightForestLabel bought ∧
      out.2 ≤ expandForestLinksFromRowsWordBudget n arcs.length h bought.card rows.length := by
  simpa only [inter_eq_left.mpr complete] using expandForestLinksFromRowsWithWordWork_spec arcs n size bought rows

end OnlineReachabilityPreservers
