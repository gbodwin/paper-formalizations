import OnlineReachabilityPreservers.SteinerBinaryFinOutputWork
import OnlineReachabilityPreservers.SteinerHubRouteWork

/-! Use the verified binary thin graph in the finite late-phase evaluator. -/

namespace OnlineReachabilityPreservers

/-- Keep the list-backed classification, hub routing and thick escape.
Use the indexed binary thin evaluator for the selected thin trace. -/
def lateSteinerWithBinaryThinWork {n : ℕ} (G : Arcs (Fin n)) (arcs : {r : List (Fin n × Fin n) // r.Nodup})
    (τ m fuel : ℕ) (hm : m = G.card) (vertices : List (Fin n)) (hubs : Finset (Fin n))
    (base ceiling factor : List Bool) (index : G ≃ Fin G.card) (sample : Fin G.card → Fin G.card)
    (D : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
  lateSteinerWithListHubWorkUsing arcs n τ vertices hubs
    (fun thin => binaryThinTypedGraphWithWork G arcs.val thin vertices base ceiling factor m fuel hm index sample) D

theorem binaryThinTypedGraphWorkBudget_mono (n arcs vertices base ceiling factor supply : ℕ) :
    Monotone (binaryThinTypedGraphWorkBudget n arcs vertices base ceiling factor supply) := by
  intro a b ordered
  unfold binaryThinTypedGraphWorkBudget binaryThinRoundFromFinInputWorkBudget binaryFinArcEncodingWorkBudget
    binaryThinRoundFromEmptyWorkBudget binaryThinRoundRunWorkBudget
  gcongr

/-- The late evaluator with a binary thin step agrees with the paper's
assembled algorithm at cutoff zero. The combined bound adds hub word work
to the measured binary thin work at the supplied widths. -/
theorem lateSteinerWithBinaryThinWork_refines {n : ℕ} (arcs : {r : List (Fin n × Fin n) // r.Nodup})
    (early : EarlySteinerRule arcs.val.toFinset) (τ : ℕ) (vertices : List (Fin n))
    (simple : vertices.Nodup) (complete : ∀ v, v ∈ vertices) (hubs : Finset (Fin n))
    (base ceiling factor : List Bool) (size : binaryWordValue base = n)
    (supply : binaryWordValue ceiling = arcs.val.toFinset.card) (factorEq : binaryWordValue factor = thinRoundingFactor n τ)
    (index : arcs.val.toFinset ≃ Fin arcs.val.toFinset.card) (sample : Fin arcs.val.toFinset.card → Fin arcs.val.toFinset.card)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach arcs.val.toFinset d.1 d.2) :
    let G := arcs.val.toFinset
    let fuel := G.card*(G.card.log2+1)+1
    let out := lateSteinerWithBinaryThinWork G arcs τ G.card fuel rfl vertices hubs base ceiling factor index sample D
    out.1 = assembledSteiner early 0 τ hubs (fun e => sample (index e)) D ∧
    out.2 ≤ lateHubRoutingWordBudget n arcs.val.length D.length+
      binaryThinTypedGraphWorkBudget n arcs.val.length vertices.length base.length ceiling.length factor.length G.card D.length := by
  let G := arcs.val.toFinset
  let fuel := G.card*(G.card.log2+1)+1
  let round (thin : List (Fin n × Fin n)) :=
    binaryThinTypedGraphWithWork G arcs.val thin vertices base ceiling factor G.card fuel rfl index sample
  let budget := binaryThinTypedGraphWorkBudget n arcs.val.length vertices.length base.length ceiling.length factor.length G.card
  let trace := steinerPhaseTraces early 0 hubs D
  have roundWork (thin : List (Fin n × Fin n)) (ok : ∀ d ∈ thin, Reach G d.1 d.2) : (round thin).2 ≤ budget thin.length :=
    (binaryThinTypedGraphWithWork_refines arcs.val thin arcs.property ok vertices complete base ceiling factor size supply
      index sample).2
  have mono := binaryThinTypedGraphWorkBudget_mono n arcs.val.length vertices.length base.length ceiling.length factor.length G.card
  obtain ⟨shape,work⟩ := lateSteinerWithListHubWorkUsing_spec arcs τ vertices simple complete hubs early round D budget mono
    roundWork feasible
  have thinFeasible : ∀ d ∈ trace.thin, Reach G d.1 d.2 :=
    fun d present => feasible d (steinerPhaseTraces_thin_subset early 0 hubs D present)
  have rounded : (round trace.thin).1 = thinRoundRun G (thinRoundingFactor n τ) (fun e => sample (index e)) trace.thin := by
    have output := (binaryThinTypedGraphWithWork_refines arcs.val trace.thin arcs.property thinFeasible vertices complete
      base ceiling factor size supply index sample).1
    change (round trace.thin).1 = _ at output
    rw [factorEq] at output
    exact output
  refine ⟨?_,?_⟩
  · change (lateSteinerWithListHubWorkUsing arcs n τ vertices hubs round D).1 = _
    rw [assembledSteiner_zero_cutoff]
    change (lateSteinerWithListHubWorkUsing arcs (Fintype.card (Fin n)) τ vertices hubs round D).1 =
      (if trace.thin.any (fun d => decide (τ < (reachInterval G d).card)) then G
      else hubPreserver G hubs trace.hits ∪ (round trace.thin).1) at shape
    rw [rounded] at shape
    simpa only [Fintype.card_fin] using shape
  · simpa only [lateSteinerWithBinaryThinWork,Fintype.card_fin] using work

end OnlineReachabilityPreservers
