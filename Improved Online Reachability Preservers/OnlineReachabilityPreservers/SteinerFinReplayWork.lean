import OnlineReachabilityPreservers.SteinerFinPreparationWork
import OnlineReachabilityPreservers.SteinerSeedDecoderWork

/-! Use the explicit list preparation in fixed-budget Steiner prefix replay. -/

namespace OnlineReachabilityPreservers

/-- Build the distance rows and forest once before decoding and use the
same weighted plan throughout replay. For an input arc list, its extra work
counts the list-backed hop computation and the paired template construction. -/
def completeFinSteinerReplayWithPreparationWork {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let prepared := prepareFinSteinerForSeedWithWordWork G arcs same height
  completeSteinerReplayWithDecoderWorkFromPreparation G height n m (by simp) hm prepared bits D

/-- The new preparation preserves every prefix graph, the per-prefix work
and the decoder tally, including on bit exhaustion. -/
theorem completeFinSteinerReplayWithPreparationWork_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithPreparationWork G arcs same height m hm bits D
    let old := completeSteinerReplayWithCachedDecoderWork G height n m (by simp) hm bits D
    out = ((old.1.1,out.1.2.1,out.1.2.2.1,old.1.2.2.2),old.2) ∧
      out.1.2.1 ≤ distanceTableListWorkPolynomial n arcs.length+8*n+9 ∧
      out.1.2.2.1 ≤ heightForestListDistanceWorkPolynomial n height 1+5 := by
  let prepared := prepareFinSteinerForSeedWithWordWork G arcs same height
  obtain ⟨planEq,table,forest⟩ := prepareFinSteinerForSeedWithWordWork_spec G arcs same height
  have execution := completeSteinerReplayWithDecoderWorkFromPreparation_eq G height n m (by simp) hm
    prepared prepared.2.2.1 prepared.2.2.2.1 planEq bits D
  exact ⟨execution,table,forest⟩

/-- The cumulative measured work includes parsing the bit word, building
the hop table and paired forest, and the existing search and table tallies. -/
def completeFinSteinerPreparationWorkPolynomial (n m raw height p : ℕ) : ℕ :=
  completeSteinerWeightWorkPolynomial n m height p+completeSteinerCachedDecoderWorkPolynomial n m height+
    (distanceTableListWorkPolynomial n raw+8*n+9)+(heightForestListDistanceWorkPolynomial n height 1+5)

/-- The unchanged fixed-budget algorithm returns the same prefix outputs.
The explicit preparation and the previously metered actions have one
polynomial bound at each fixed height. -/
theorem completeFinSteinerReplayWithPreparationWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithPreparationWork G arcs same height m hm bits D
    out.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (out.1.1.map Prod.snd).sum+out.1.2.1+out.1.2.2.1+out.1.2.2.2+out.2 ≤
        completeFinSteinerPreparationWorkPolynomial n m arcs.length height D.length := by
  let old := completeSteinerReplayWithCachedDecoderWork G height n m (by simp) hm bits D
  let out := completeFinSteinerReplayWithPreparationWork G arcs same height m hm bits D
  obtain ⟨matching,table,forest⟩ := completeFinSteinerReplayWithPreparationWork_spec G arcs same height m hm bits D
  obtain ⟨prefixes,work⟩ := completeSteinerReplayWithCachedDecoderWork_prefixes G height n m
    (by simp) hm bits D feasible
  have rounds : out.1.1 = old.1.1 := congrArg (fun x => x.1.1) matching
  have weights : out.1.2.2.2 = old.1.2.2.2 := congrArg (fun x => x.1.2.2.2) matching
  have decoder : out.2 = old.2 := congrArg (fun x => x.2) matching
  change (out.1.1.map Prod.fst = _) ∧
    (out.1.1.map Prod.snd).sum+out.1.2.1+out.1.2.2.1+out.1.2.2.2+out.2 ≤ _
  rw [rounds,weights,decoder]
  refine ⟨prefixes,?_⟩
  change (old.1.1.map Prod.snd).sum+old.1.2.1+old.1.2.2.1+old.1.2.2.2+old.2 ≤ _ at work
  change out.1.2.1 ≤ _ at table
  change out.1.2.2.1 ≤ _ at forest
  unfold completeFinSteinerPreparationWorkPolynomial
  omega

end OnlineReachabilityPreservers
