import OnlineReachabilityPreservers.SteinerCompleteReplay
import OnlineReachabilityPreservers.SteinerDistanceTable

/-! Reuse the early distance table across the full sequence of arrival prefixes. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Share the distance table and paired template across all prefixes, and
report the arc inspections and template key comparisons separately. -/
def completeSteinerPrefixSearchReplayWithTemplateWork (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  let prepared := prepareEarlyDistanceTableWithTemplateWork G height sample
  let evaluate := completeSteinerDrawRunWithSearchWorkFromEarly G prepared.1 draw thin
  (D.inits.map evaluate,prepared.2.1,prepared.2.2)

theorem completeSteinerPrefixSearchReplayWithTemplateWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) :
    let out := completeSteinerPrefixSearchReplayWithTemplateWork G height sample draw thin D
    let n := Fintype.card V
    out.1 = completeSteinerPrefixSearchReplay G height sample draw thin D ∧
      out.2.1 ≤ n^2*((n+1)*n*G.card) ∧
      out.2.2 ≤ n*(2*Fintype.card (HeightNode V height)*height*n^2) := by
  obtain ⟨replay,build,template⟩ := prepareEarlyDistanceTableWithTemplateWork_spec G height sample
  refine ⟨?_,build.le.trans (distanceTableWithSearchWork_bound G),template⟩
  simp only [completeSteinerPrefixSearchReplayWithTemplateWork, replay, completeSteinerPrefixSearchReplay]
  rfl

/-- One table and paired template serve all the prefixes. The second field
charges the table's original-graph searches once, outside the prefix list. -/
def completeSteinerPrefixSearchReplayWithDistanceTable (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) : List (Arcs V × ℕ) × ℕ :=
  let prepared := prepareEarlyDistanceTable G height sample
  let evaluate := completeSteinerDrawRunWithSearchWorkFromEarly G prepared.1 draw thin
  (D.inits.map evaluate,prepared.2)

theorem completeSteinerPrefixSearchReplayWithDistanceTable_eq (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) :
    completeSteinerPrefixSearchReplayWithDistanceTable G height sample draw thin D =
      (completeSteinerPrefixSearchReplay G height sample draw thin D,(distanceTableWithSearchWork G).2) := by
  simp only [completeSteinerPrefixSearchReplayWithDistanceTable, prepareEarlyDistanceTable_eq,
    completeSteinerPrefixSearchReplay]
  rfl

/-- Outputs agree at every prefix and the distance searches are charged once.
The bound counts the searches and successor tests reported by the evaluator. -/
theorem completeSteinerPrefixSearchReplayWithDistanceTable_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let n := Fintype.card V
    let m := G.card
    let out := completeSteinerPrefixSearchReplayWithDistanceTable G height sample draw thin D
    out.1.map Prod.fst = D.inits.map (completeSteinerDrawRun G height sample draw thin) ∧
      (out.1.map Prod.snd).sum + out.2 ≤
        (D.length+1)*completeSteinerSearchPolynomial n m height D.length+n^2*((n+1)*n*m) := by
  rw [completeSteinerPrefixSearchReplayWithDistanceTable_eq]
  have ordinary := completeSteinerPrefixSearchReplay_spec G height sample draw thin D feasible
  exact ⟨ordinary.1,Nat.add_le_add ordinary.2 (distanceTableWithSearchWork_bound G)⟩

/-- Share preparation across all arrivals and include the rounding weight
reads in the search charge at each prefix. -/
def completeSteinerPrefixSearchReplayWithRoundingWork (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  let prepared := prepareEarlyDistanceTableWithRoundingWork G height sample
  let evaluate := completeSteinerDrawRunWithSearchWorkFromEarly G prepared.1 draw thin
  (D.inits.map evaluate,prepared.2.1,prepared.2.2)

/-- The same prefix graphs, with an explicit polynomial for the charged
searches and rounding reads at fixed height. The table-build and template
charges are reported once. -/
theorem completeSteinerPrefixSearchReplayWithRoundingWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let n := Fintype.card V
    let m := G.card
    let p := D.length
    let out := completeSteinerPrefixSearchReplayWithRoundingWork G height sample draw thin D
    out.1.map Prod.fst = D.inits.map (completeSteinerDrawRun G height sample draw thin) ∧
      (out.1.map Prod.snd).sum ≤ (p+1)*completeSteinerSearchPolynomial n m height p+
        (p+1)*((p+1)*roundingComparisonPolynomial n height) ∧
      out.2.1 ≤ n^2*((n+1)*n*m) ∧
      out.2.2 ≤ n*(2*Fintype.card (HeightNode V height)*height*n^2) := by
  let plain := prepareEarlyDistanceTableWithTemplateWork G height sample
  let next := prepareEarlyDistanceTableWithRoundingWork G height sample
  obtain ⟨samePrep,perPrefix⟩ := prepareEarlyDistanceTableWithRoundingWork_spec G height sample
  obtain ⟨plainEq,buildEq,template⟩ := prepareEarlyDistanceTableWithTemplateWork_spec G height sample
  obtain ⟨graphs,charges⟩ := completeSteinerPrefixSearchReplay_spec G height sample draw thin D feasible
  obtain ⟨same,extra⟩ := completeSteinerPrefixSearchReplayFromEarly_compare G plain.1 next.1
    (roundingComparisonPolynomial (Fintype.card V) height) perPrefix draw thin D
  have original : D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G plain.1 draw thin) =
      completeSteinerPrefixSearchReplay G height sample draw thin D := by
    rw [show plain.1 = _ from plainEq]
    rfl
  rw [original] at same extra
  have prepEq : next.2 = plain.2 := samePrep
  have arcEq : plain.2.1 = (distanceTableWithSearchWork G).2 := buildEq
  refine ⟨same.trans graphs,extra.trans (Nat.add_le_add_right charges _),?_,?_⟩
  · change next.2.1 ≤ _
    rw [prepEq,arcEq]
    exact distanceTableWithSearchWork_bound G
  · change next.2.2 ≤ _
    rw [prepEq]
    exact template

/-- Include both the rounding and cached-capacity weight reads in the
search charge at each prefix. The two shared preparation charges are separate. -/
def completeSteinerPrefixSearchReplayWithCapacityWork (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  let prepared := prepareEarlyDistanceTableWithCapacityWork G height sample
  let evaluate := completeSteinerDrawRunWithSearchWorkFromEarly G prepared.1 draw thin
  (D.inits.map evaluate,prepared.2.1,prepared.2.2)

theorem completeSteinerPrefixSearchReplayWithCapacityWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let n := Fintype.card V
    let m := G.card
    let p := D.length
    let out := completeSteinerPrefixSearchReplayWithCapacityWork G height sample draw thin D
    out.1.map Prod.fst = D.inits.map (completeSteinerDrawRun G height sample draw thin) ∧
      (out.1.map Prod.snd).sum ≤ (p+1)*completeSteinerSearchPolynomial n m height p+
        (p+1)*((p+1)*roundingComparisonPolynomial n height)+
        (p+1)*((p+1)*(p*capacityComparisonPolynomial n height)) ∧
      out.2.1 ≤ n^2*((n+1)*n*m) ∧
      out.2.2 ≤ n*(2*Fintype.card (HeightNode V height)*height*n^2) := by
  let prior := prepareEarlyDistanceTableWithRoundingWork G height sample
  let next := prepareEarlyDistanceTableWithCapacityWork G height sample
  let C := capacityComparisonPolynomial (Fintype.card V) height
  obtain ⟨samePrep,early⟩ := prepareEarlyDistanceTableWithCapacityWork_spec G height sample
  obtain ⟨graphs,charges,prepared,template⟩ :=
    completeSteinerPrefixSearchReplayWithRoundingWork_spec G height sample draw thin D feasible
  have compare (P : List (V × V)) (short : P.length ≤ D.length) :
      (next.1 P).1 = (prior.1 P).1 ∧ (next.1 P).2 ≤ (prior.1 P).2+(P.length+1)*(D.length*C) := by
    obtain ⟨same,extra⟩ := early P
    exact ⟨same,extra.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right C short)) _)⟩
  obtain ⟨same,extra⟩ := completeSteinerPrefixSearchReplayFromEarly_compareOnLengths G prior.1 next.1
    (D.length*C) draw thin D compare
  have prepEq : next.2 = prior.2 := samePrep
  refine ⟨same.trans graphs,extra.trans (Nat.add_le_add_right charges _),?_,?_⟩
  · change next.2.1 ≤ _
    exact prepEq.symm ▸ prepared
  · change next.2.2 ≤ _
    exact prepEq.symm ▸ template

/-- Complete prefix replay with the original distance-table reads charged in
template setup, weight preparation, weighted separation, and rounding. -/
def completeSteinerPrefixSearchReplayWithWeightWork (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ × ℕ :=
  let prepared := prepareEarlyDistanceTableWithWeightWork G height sample
  let evaluate := completeSteinerDrawRunWithSearchWorkFromEarly G prepared.1 draw thin
  (D.inits.map evaluate,prepared.2.1,prepared.2.2.1,prepared.2.2.2)

theorem completeSteinerPrefixSearchReplayWithWeightWork_eq (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) :
    let out := completeSteinerPrefixSearchReplayWithWeightWork G height sample draw thin D
    let old := completeSteinerPrefixSearchReplayWithCapacityWork G height sample draw thin D
    out.1 = old.1 ∧ out.2.1 = old.2.1 ∧ out.2.2.1 = old.2.2 ∧
      out.2.2.2 ≤ Fintype.card (HeightForestVertex V height)^2 * Fintype.card V^2 := by
  obtain ⟨same,build,template,weight⟩ := prepareEarlyDistanceTableWithWeightWork_spec G height sample
  exact ⟨congrArg (fun early => D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G early draw thin))
    same,build,template,weight⟩

theorem completeSteinerPrefixSearchReplayWithWeightWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let n := Fintype.card V
    let m := G.card
    let p := D.length
    let out := completeSteinerPrefixSearchReplayWithWeightWork G height sample draw thin D
    out.1.map Prod.fst = D.inits.map (completeSteinerDrawRun G height sample draw thin) ∧
      (out.1.map Prod.snd).sum ≤ (p+1)*completeSteinerSearchPolynomial n m height p+
        (p+1)*((p+1)*roundingComparisonPolynomial n height)+
        (p+1)*((p+1)*(p*capacityComparisonPolynomial n height)) ∧
      out.2.1 ≤ n^2*((n+1)*n*m) ∧
      out.2.2.1 ≤ n*(2*Fintype.card (HeightNode V height)*height*n^2) ∧
      out.2.2.2 ≤ Fintype.card (HeightForestVertex V height)^2*n^2 := by
  obtain ⟨same,buildEq,templateEq,weight⟩ := completeSteinerPrefixSearchReplayWithWeightWork_eq G height sample draw thin D
  obtain ⟨graphs,charges,build,template⟩ :=
    completeSteinerPrefixSearchReplayWithCapacityWork_spec G height sample draw thin D feasible
  exact ⟨same.symm ▸ graphs,same.symm ▸ charges,buildEq.symm ▸ build,templateEq.symm ▸ template,weight⟩

/-- Bound the measured searches and original table reads by one polynomial
for fixed height. The three preparation terms are charged once. -/
def completeSteinerWeightWorkPolynomial (n m height p : ℕ) : ℕ :=
  let H := (height+1)*n^height
  let F := (n*2)*H
  (p+1)*completeSteinerSearchPolynomial n m height p+
    (p+1)*((p+1)*roundingComparisonPolynomial n height)+
    (p+1)*((p+1)*(p*capacityComparisonPolynomial n height))+
    n^2*((n+1)*n*m)+n*(2*H*height*n^2)+F^2*n^2

theorem completeSteinerPrefixSearchReplayWithWeightWork_polynomial (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (draw : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let n := Fintype.card V
    let out := completeSteinerPrefixSearchReplayWithWeightWork G height sample draw thin D
    out.1.map Prod.fst = D.inits.map (completeSteinerDrawRun G height sample draw thin) ∧
      (out.1.map Prod.snd).sum+out.2.1+out.2.2.1+out.2.2.2 ≤
        completeSteinerWeightWorkPolynomial n G.card height D.length := by
  let n := Fintype.card V
  let H := (height+1)*n^height
  let F := (n*2)*H
  let out := completeSteinerPrefixSearchReplayWithWeightWork G height sample draw thin D
  obtain ⟨graphs,charges,build,template,weights⟩ :=
    completeSteinerPrefixSearchReplayWithWeightWork_spec G height sample draw thin D feasible
  have forest : Fintype.card (HeightForestVertex V height) ≤ F := by
    cases isEmpty_or_nonempty V with
    | inl empty => simp [HeightForestVertex]
    | inr ne => exact heightForestVertex_card_le V height
  have templateCap : out.2.2.1 ≤ n*(2*H*height*n^2) := by
    apply template.trans
    change n*(2*Fintype.card (HeightNode V height)*height*n^2) ≤ n*(2*H*height*n^2)
    cases isEmpty_or_nonempty V with
    | inl empty => simp [n]
    | inr ne =>
      have histories : Fintype.card (HeightNode V height) ≤ H := heightNode_card_le V height
      gcongr
  have weightCap : out.2.2.2 ≤ F^2*n^2 :=
    weights.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left forest _))
  exact ⟨graphs,Nat.add_le_add (Nat.add_le_add (Nat.add_le_add charges build) templateCap) weightCap⟩

end OnlineReachabilityPreservers
