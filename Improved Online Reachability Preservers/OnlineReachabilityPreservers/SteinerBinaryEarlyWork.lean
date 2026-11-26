import OnlineReachabilityPreservers.SteinerBinaryForestRunWork
import OnlineReachabilityPreservers.SteinerEarlyReplay

/-! Use binary weighted forest evaluations in the exact early prefix replay. -/

namespace OnlineReachabilityPreservers

open Finset

local instance binaryEarlyHeightDecidableEq {n h : ℕ} : DecidableEq (HeightForestVertex (Fin n) h) :=
  (inferInstance : LinearOrder (HeightForestVertex (Fin n) h)).toDecidableEq

local instance binaryEarlyNetworkDecidableEq {n h : ℕ} : DecidableEq (ForestNetworkVertex (Fin n) h) :=
  (inferInstance : LinearOrder (ForestNetworkVertex (Fin n) h)).toDecidableEq

/-- Evaluate each nonempty early prefix with the binary forest solver.
Use the existing prefix validation, purchases, and expansion. -/
def binaryEarlyRoundedGraphWithWork {n h : ℕ} (G : Arcs (Fin n))
    (links : {es : List (HeightForestVertex (Fin n) h × HeightForestVertex (Fin n) h) // es.Nodup})
    (paid free : Arcs (ForestNetworkVertex (Fin n) h))
    (freeRows : List (ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h))
    (read : Fin n × Fin n → ℕ × ℕ) (scale trials : ℕ)
    (samples : ForestTrialArrayWithSeedWork (Fin n) h scale trials) (D : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ × ℕ :=
  earlyRoundedGraphWithSeedReadsFromMetric G h (fun P =>
    let run := binaryForestRoundWithWork links paid free freeRows read scale trials samples P
    (run.1,0,run.2.1+run.2.2+5)) D

/-- Include the weighted tally, rounding, and reached trial reads for one
early metric evaluation. -/
def binaryEarlyMetricWorkBudget {n h : ℕ} (G : Arcs (Fin n))
    (paid free : Arcs (ForestNetworkVertex (Fin n) h)) (freeRows readFee seedFee : ℕ)
    (read : Fin n × Fin n → ℕ × ℕ) (P : List (Fin n × Fin n)) : ℕ :=
  let labels := binaryFinForestNetworkLabelsWithWork n h
  let keys := (finForestNetworkRowsWithWordWork n h).keys.length
  let updates := P.length*weightedCoverFuel paid (forestNetworkWeight G)
  let scale := forestScale G h
  let trials := earlyTrialCount (Fin n) h
  let links := (heightForest G h).card
  (binaryForestFractionalWithWork h paid free read P).2+
    binaryForestRoundAdditionalWorkBudget h labels.count keys freeRows labels.width n.size
      (n.size+updates*(1+updates+1)) scale trials links readFee+
    trials*(links*((scale.log2+1)*((h+2)*seedFee)))+5

/-- With exact prepared inputs, the early replay reproduces the paper's
expanded early graph, including its full-graph fallback. -/
theorem binaryEarlyRoundedGraphWithWork_refines {n h : ℕ} (G : Arcs (Fin n))
    (links : {es : List (HeightForestVertex (Fin n) h × HeightForestVertex (Fin n) h) // es.Nodup})
    (linksExact : links.val.toFinset = heightForest G h)
    (paid free : Arcs (ForestNetworkVertex (Fin n) h))
    (paidExact : paid = forestNetworkPriced G (heightForest G h)) (freeExact : free = forestNetworkZero G h)
    (freeRows : List (ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h))
    (freeAsSet : freeRows.toFinset = free)
    (read : Fin n × Fin n → ℕ × ℕ) (readFee : ℕ)
    (readExact : ∀ e, (read e).1 = hops G e.1 e.2) (readWork : ∀ e, (read e).2 ≤ readFee)
    (samples : ForestTrialArrayWithSeedWork (Fin n) h (forestScale G h) (earlyTrialCount (Fin n) h))
    (seedFee : ℕ) (seedWork : ∀ i, forestSampleWorkBound (samples i) seedFee) (D : List (Fin n × Fin n)) :
    let scale := forestScale G h
    let sample : EarlyRoundSample G h := fun i => forestRoundingSampleValues scale (samples i)
    let out := binaryEarlyRoundedGraphWithWork G links paid free freeRows read scale (earlyTrialCount (Fin n) h) samples D
    let B := ∑ P ∈ D.inits.toFinset, binaryEarlyMetricWorkBudget G paid free freeRows.length readFee seedFee read P
    out.1 = earlyRoundedGraph G h D sample ∧
    out.2.1 ≤ (earlyRoundedGraphWithSearchWork G h sample D).2 ∧ out.2.2 ≤ (D.length+1)*B := by
  let scale := forestScale G h
  let trials := earlyTrialCount (Fin n) h
  let sample : EarlyRoundSample G h := fun i => forestRoundingSampleValues scale (samples i)
  let run := binaryForestRoundWithWork links paid free freeRows read scale trials samples
  let next := fun P => ((run P).1,0,(run P).2.1+(run P).2.2+5)
  let earlier := earlyMetricWithSearchWork G h sample
  let prior := fun P => ((earlier P).1,(earlier P).2,0)
  let budget := binaryEarlyMetricWorkBudget G paid free freeRows.length readFee seedFee read
  let B := ∑ P ∈ D.inits.toFinset, budget P
  have evaluate (P : List (Fin n × Fin n)) :=
    binaryForestRoundWithWork_refines G links linksExact paid free paidExact freeExact freeRows freeAsSet read
      readFee readExact readWork scale trials (forestScale_pos G h) samples seedFee seedWork P
  have records (P : List (Fin n × Fin n)) (_ : P ∈ D.inits) :
      (next P).1 = (prior P).1 ∧ (next P).2.1 ≤ (prior P).2.1 := by
    have history := (forestFractionalRunWithSearchWork_spec G h P).1
    have graph : (earlier P).1 = roundedForestTrials G (forestFractionalRun G h P).1 scale trials sample := by
      dsimp only [earlier,earlyMetricWithSearchWork]
      rw [history]
    exact ⟨(evaluate P).1.trans graph.symm,Nat.zero_le _⟩
  have work (P : List (Fin n × Fin n)) (inside : P ∈ D.inits) : (next P).2.2 ≤ B := by
    obtain ⟨_,rounded,reads⟩ := evaluate P
    have allowance : (next P).2.2 ≤ budget P := Nat.add_le_add_right (Nat.add_le_add rounded reads) 5
    exact allowance.trans (single_le_sum (f := budget) (fun _ _ => Nat.zero_le _) (List.mem_toFinset.mpr inside))
  obtain ⟨record,legacy,tally⟩ := earlyRoundedGraphWithSeedReadsFromMetric_compare G h next prior D B records work
  obtain ⟨priorRecord,_⟩ := earlyRoundedGraphWithSeedReadsFromMetric_spec G h prior D 0 (by simp [prior])
  have exactGraph := (earlyRoundedGraphWithSearchWork_spec G h sample D).1
  exact ⟨record.trans ((congrArg Prod.fst priorRecord).trans exactGraph),
    legacy.trans_eq (congrArg Prod.snd priorRecord),tally⟩

end OnlineReachabilityPreservers
