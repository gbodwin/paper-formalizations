import OnlineReachabilityPreservers.AssignmentListQuotaWork
import OnlineReachabilityPreservers.AssignmentListRouteWork
import OnlineReachabilityPreservers.AssignmentQuotaArithmeticWork
import OnlineReachabilityPreservers.RestrictedNonAdaptive

/-! Count exact single-path queries for both endpoint promises in Theorem 5. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def sinkAssignmentDomainWithWordWork (G : List (V × V)) (vertices sinks : List V) :
    List (V × V) × ℕ :=
  let table := componentLabelTableWithWordWork G vertices
  let targets := projectVerticesWithWordWork table.1 sinks
  (vertices ×ˢ targets.1, table.2+targets.2+
    18*(vertices.length*sinks.length)+14*(vertices.length+sinks.length)+12)

private def sinkAssignmentDomainWordBudget (n m σ : ℕ) : ℕ :=
  prepareCondensationWordBudget n m + (4*(σ*(n+1))+8*σ+4) + 18*(n*σ)+14*(n+σ)+12

private theorem sinkAssignmentDomainWithWordWork_spec (G : List (V × V)) (vertices sinks : List V)
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let out := sinkAssignmentDomainWithWordWork G vertices sinks
    out.1.toFinset = univ ×ˢ sinks.toFinset.image (componentLabel G.toFinset) ∧
      out.1.length = n*sinks.length ∧ out.2 ≤ sinkAssignmentDomainWordBudget n G.length sinks.length := by
  let n := Fintype.card V
  let table := componentLabelTableWithWordWork G vertices
  let targets := projectVerticesWithWordWork table.1 sinks
  have cover : vertices.toFinset = univ := by ext v; simp [complete v]
  have count : vertices.length = n := by rw [← List.toFinset_card_of_nodup unique, cover, card_univ]
  obtain ⟨labels, labelWork⟩ := componentLabelTableWithWordWork_spec G vertices unique complete
  obtain ⟨projected, projectedWork⟩ :=
    projectVerticesWithWordWork_spec (componentLabel G.toFinset) vertices sinks complete
  have targetEq : targets.1 = sinks.map (componentLabel G.toFinset) := by
    unfold targets
    rw [show table.1 = _ from labels]
    exact projected
  have targetCost : targets.2 ≤ 4*(sinks.length*(n+1))+8*sinks.length+4 := by
    unfold targets
    rw [show table.1 = _ from labels, ← count]
    exact projectedWork
  have prep : table.2 ≤ prepareCondensationWordBudget n G.length :=
    labelWork.trans (by dsimp only [n]; unfold prepareCondensationWordBudget; omega)
  refine ⟨?_, ?_, ?_⟩
  · change (vertices ×ˢ targets.1).toFinset = _
    rw [targetEq]
    ext ⟨u, v⟩
    simp only [List.mem_toFinset, List.mem_product, List.mem_map, complete u,
      true_and, mem_product, mem_univ, mem_image]
  · change (vertices ×ˢ targets.1).length = _
    rw [List.length_product, targetEq, List.length_map, count]
  · change table.2+targets.2+18*(vertices.length*sinks.length)+14*(vertices.length+sinks.length)+12 ≤ _
    rw [count]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add prep targetCost) _) _) _

/-- Choose a path using the given total and allowed sinks. The candidate
domain is the product of all vertices and the projected sink list. -/
def knownSinkPathWithWordWork (G : List (V × V)) (vertices sinks : List V) (p : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let n := vertices.length
  let σ := sinks.length
  let root := natSqrtWithWordWork (2*n*σ*p)
  let domain := sinkAssignmentDomainWithWordWork G vertices sinks
  let lifted := liftCoreListWithWordWork (knownQuotaArcsWithWordWork domain.1 p (n+root.1)) G vertices [d]
  let routed := routePathListWithWordWork lifted.1 d.1 d.2 n
  (routed.1, root.2+domain.2+lifted.2+routed.2+3*n+3*σ+22)

def knownSinkPathWordBudget (n m σ p : ℕ) : ℕ :=
  (20*(2*n*σ*p+1)+5) + sinkAssignmentDomainWordBudget n m σ +
    (1+liftCoreWordBudget n m 1+knownQuotaArcWordBudget n m (n*σ) p) +
    routePathListWordBudget n m+3*n+3*σ+22

private theorem knownSinkPathWordBudget_mono_quota (n m σ : ℕ) :
    Monotone (knownSinkPathWordBudget n m σ) := by
  intro a b ordered
  have quota := knownQuotaArcWordBudget_mono_quota n m (n*σ) ordered
  unfold knownSinkPathWordBudget
  gcongr

theorem knownSinkPathWithWordWork_spec (G : List (V × V)) (vertices sinks : List V) (p : ℕ) (d : V × V)
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (sinkSet : sinks.Nodup) :
    let n := Fintype.card V
    let out := knownSinkPathWithWordWork G vertices sinks p d
    out.1 = knownSinkPath G.toFinset sinks.toFinset p d ∧
      out.2 ≤ knownSinkPathWordBudget n G.length sinks.length p := by
  let n := Fintype.card V
  let σ := sinks.length
  let root := natSqrtWithWordWork (2*n*σ*p)
  let domain := sinkAssignmentDomainWithWordWork G vertices sinks
  let run := knownQuotaArcsWithWordWork domain.1 p (n+root.1)
  let plain := knownQuotaArcs domain.1.toFinset p (n+root.1)
  let lifted := liftCoreListWithWordWork run G vertices [d]
  let routed := routePathListWithWordWork lifted.1 d.1 d.2 n
  have cover : vertices.toFinset = univ := by ext v; simp [complete v]
  have count : vertices.length = n := by rw [← List.toFinset_card_of_nodup unique, cover, card_univ]
  obtain ⟨rootEq, rootWork⟩ := natSqrtWithWordWork_spec (2*n*σ*p)
  have quota : n+root.1 = endpointBudget n sinks.toFinset.card p := by
    rw [show root.1 = _ from rootEq, List.toFinset_card_of_nodup sinkSet]
    rfl
  obtain ⟨domainEq, domainLength, domainWork⟩ := sinkAssignmentDomainWithWordWork_spec G vertices sinks unique complete
  obtain ⟨simpleLift, liftedSet, liftWork⟩ := liftCoreListWithWordWork_spec run plain
    (fun a b _ => knownQuotaArcWordBudget a b domain.1.length p)
    (fun K D _ => knownQuotaArcsWithWordWork_spec domain.1 p (n+root.1) K D)
    (knownQuotaArcs_subset domain.1.toFinset p (n+root.1))
    (fun a _ => knownQuotaArcWordBudget_mono_arcs a domain.1.length p) G vertices [d] unique complete
  have liftEq : lifted.1.toFinset = liftedRun plain G.toFinset [d] := liftedSet
  have sub : lifted.1.toFinset ⊆ G.toFinset := by
    rw [liftEq]
    exact union_subset (connectors_subset _) (liftedArcs_subset _ _)
  have length : lifted.1.length ≤ G.length := by
    rw [← List.toFinset_card_of_nodup simpleLift]
    exact (card_le_card sub).trans (List.toFinset_card_le _)
  obtain ⟨routeEq, routeWork⟩ := routePathListWithWordWork_spec lifted.1 d.1 d.2
  have liftedCap : lifted.2 ≤ 1+liftCoreWordBudget n G.length 1+knownQuotaArcWordBudget n G.length (n*σ) p := by
    change lifted.2 ≤ 1+liftCoreWordBudget n G.length 1+knownQuotaArcWordBudget n G.length domain.1.length p at liftWork
    rw [show domain.1.length = n*σ from domainLength] at liftWork
    exact liftWork
  have routeCap : routed.2 ≤ routePathListWordBudget n G.length :=
    routeWork.trans (routePathListWordBudget_mono_arcs n length)
  dsimp only [knownSinkPathWithWordWork]
  rw [count]
  change routed.1 = _ ∧ root.2+domain.2+lifted.2+routed.2+3*n+3*σ+22 ≤ _
  constructor
  · rw [show routed.1 = _ from routeEq, liftEq]
    unfold plain
    rw [show domain.1.toFinset = _ from domainEq, quota]
    rfl
  · unfold knownSinkPathWordBudget
    gcongr

/-- Evaluate the restricted selector at the least dyadic quota for the given
arrival index, charging the base arithmetic and doubling. -/
def indexedSinkPathWithWordWork (G : List (V × V)) (vertices sinks : List V) (i : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let n := vertices.length
  let σ := sinks.length
  let quota := indexQuotaWithWordWork (endpointBase n σ) i
  let assigned := knownSinkPathWithWordWork G vertices sinks quota.1 d
  (assigned.1,quota.2+assigned.2+3*n+3*σ+14)

def indexedSinkPathWordBudget (n m σ i : ℕ) : ℕ :=
  (1+6*(i+1))+knownSinkPathWordBudget n m σ (n+1+2*(i+1))+3*n+3*σ+14

theorem indexedSinkPathWithWordWork_spec (G : List (V × V)) (vertices sinks : List V) (i : ℕ) (d : V × V)
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (sinkSet : sinks.Nodup) :
    let n := Fintype.card V
    let out := indexedSinkPathWithWordWork G vertices sinks i d
    out.1 = indexedSinkPath G.toFinset sinks.toFinset i d ∧
      out.2 ≤ indexedSinkPathWordBudget n G.length sinks.length i := by
  let n := Fintype.card V
  let σ := sinks.length
  let base := endpointBase n σ
  let quota := indexQuotaWithWordWork base i
  let assigned := knownSinkPathWithWordWork G vertices sinks quota.1 d
  have cover : vertices.toFinset = univ := by ext v; simp [complete v]
  have count : vertices.length = n := by rw [← List.toFinset_card_of_nodup unique, cover, card_univ]
  have positive : 0 < base := Nat.zero_lt_one.trans_le (le_max_left _ _)
  have baseCap : base ≤ n+1 :=
    max_le (Nat.le_add_left _ _) ((Nat.div_le_self _ _).trans (Nat.le_succ _))
  obtain ⟨quotaEq, quotaWork⟩ := indexQuotaWithWordWork_spec base i positive
  have cap : quota.1 ≤ n+1+2*(i+1) := by
    rw [show quota.1 = _ from quotaEq]
    exact (indexQuota_le_add positive i).trans (Nat.add_le_add_right baseCap _)
  obtain ⟨equal, work⟩ := knownSinkPathWithWordWork_spec G vertices sinks quota.1 d unique complete sinkSet
  have spent := work.trans (knownSinkPathWordBudget_mono_quota n G.length σ cap)
  dsimp only [indexedSinkPathWithWordWork]
  rw [count]
  change assigned.1 = _ ∧ quota.2+assigned.2+3*n+3*σ+14 ≤ _
  refine ⟨?_,Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add quotaWork spent) _) _) _⟩
  rw [show assigned.1 = _ from equal, show quota.1 = _ from quotaEq]
  unfold base σ
  rw [← List.toFinset_card_of_nodup sinkSet]
  rfl

private def reverseAssignmentPathWithWordWork
    (choose : List (V × V) → V × V → Option (List (V × V)) × ℕ) (G : List (V × V)) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let selected := choose (G.map Prod.swap) d.swap
  (reversePath selected.1,selected.2+6*G.length+14*(selected.1.getD []).length+12)

private theorem reverseAssignmentPathWithWordWork_spec
    (choose : List (V × V) → V × V → Option (List (V × V)) × ℕ)
    (plain : Arcs V → V × V → Option (List (V × V))) (budget : ℕ → ℕ)
    (same : ∀ K r, (choose K r).1 = plain K.toFinset r ∧ (choose K r).2 ≤ budget K.length)
    (short : ∀ K r, ((plain K r).getD []).length ≤ Fintype.card V)
    (G : List (V × V)) (d : V × V) :
    let out := reverseAssignmentPathWithWordWork choose G d
    out.1 = reversePath (plain (reverseArcs G.toFinset) d.swap) ∧
      out.2 ≤ budget G.length+6*G.length+14*Fintype.card V+12 := by
  let selected := choose (G.map Prod.swap) d.swap
  obtain ⟨equal, work⟩ := same (G.map Prod.swap) d.swap
  have selection : selected.1 = plain (reverseArcs G.toFinset) d.swap := by
    simpa only [reverseArcList_toFinset] using equal
  have charged : selected.2 ≤ budget G.length := by simpa only [List.length_map] using work
  have length : (selected.1.getD []).length ≤ Fintype.card V := by
    rw [selection]
    exact short _ _
  exact ⟨congrArg reversePath selection, Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_right charged _) (Nat.mul_le_mul_left 14 length)) _⟩

/-- The known-total source version charges both reversing the graph and
reversing the returned path. -/
def knownSourcePathWithWordWork (G : List (V × V)) (vertices sources : List V) (p : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  reverseAssignmentPathWithWordWork (fun K => knownSinkPathWithWordWork K vertices sources p) G d

theorem knownSourcePathWithWordWork_spec (G : List (V × V)) (vertices sources : List V) (p : ℕ) (d : V × V)
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (sourceSet : sources.Nodup) :
    let n := Fintype.card V
    let out := knownSourcePathWithWordWork G vertices sources p d
    out.1 = knownSourcePath G.toFinset sources.toFinset p d ∧
      out.2 ≤ knownSinkPathWordBudget n G.length sources.length p+6*G.length+14*n+12 :=
  reverseAssignmentPathWithWordWork_spec
    (fun K => knownSinkPathWithWordWork K vertices sources p) (fun K => knownSinkPath K sources.toFinset p)
    (fun m => knownSinkPathWordBudget (Fintype.card V) m sources.length p)
    (fun K r => knownSinkPathWithWordWork_spec K vertices sources p r unique complete sourceSet)
    (fun _ _ => by unfold knownSinkPath; exact liftPath_length_le _ _ _) G d

/-- The source-restricted assignment at a zero-based arrival index. -/
def indexedSourcePathWithWordWork (G : List (V × V)) (vertices sources : List V) (i : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  reverseAssignmentPathWithWordWork (fun K => indexedSinkPathWithWordWork K vertices sources i) G d

theorem indexedSourcePathWithWordWork_spec (G : List (V × V)) (vertices sources : List V) (i : ℕ) (d : V × V)
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (sourceSet : sources.Nodup) :
    let n := Fintype.card V
    let out := indexedSourcePathWithWordWork G vertices sources i d
    out.1 = indexedSourcePath G.toFinset sources.toFinset i d ∧
      out.2 ≤ indexedSinkPathWordBudget n G.length sources.length i+6*G.length+14*n+12 :=
  reverseAssignmentPathWithWordWork_spec
    (fun K => indexedSinkPathWithWordWork K vertices sources i) (fun K => indexedSinkPath K sources.toFinset i)
    (fun m => indexedSinkPathWordBudget (Fintype.card V) m sources.length i)
    (fun K r => indexedSinkPathWithWordWork_spec K vertices sources i r unique complete sourceSet)
    (fun _ _ => by unfold indexedSinkPath; exact liftPath_length_le _ _ _) G d

theorem indexedSinkPathWordBudget_mono_index (n m σ : ℕ) :
    Monotone (indexedSinkPathWordBudget n m σ) := by
  intro i j ordered
  have quota : n+1+2*(i+1) ≤ n+1+2*(j+1) := by gcongr
  have bound := knownSinkPathWordBudget_mono_quota n m σ quota
  unfold indexedSinkPathWordBudget
  gcongr

end OnlineReachabilityPreservers
