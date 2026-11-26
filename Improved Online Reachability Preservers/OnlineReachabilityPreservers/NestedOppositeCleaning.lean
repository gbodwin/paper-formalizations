import OnlineReachabilityPreservers.ContiguousHalfCleaning

/-! Charge the incidences involved in the nested reversal obstruction. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped List

local notation "Before" => SourceAudit.BeforeIn

variable {V : Type*} [DecidableEq V] {p : ℕ}

/-- A later path reverses an opposite link inside a larger interval
reversed by another partner of the central path. -/
def LaterNestedOppositeLink (paths : Fin p → List V) (inner central : Fin p) (w v : V) : Prop :=
  central < inner ∧ OppositeNeighbors paths inner central w v ∧
    ∃ outer : Fin p, outer ≠ central ∧ outer ≠ inner ∧
      ∃ u z, Before paths central u v ∧ Before paths central w z ∧ Before paths outer z u

/-- Count only opposite-neighbor links that can participate in a later
nested reversal. Each unordered pair belongs to the set at most once. -/
def laterNestedOppositeLinkSet (paths : Fin p → List V) : Set (Sym2 V) :=
  {edge | ∃ (inner central : Fin p) (w v : V),
    edge = s(w,v) ∧ LaterNestedOppositeLink paths inner central w v}

theorem laterNestedOppositeLinkSet_subset (paths : Fin p → List V) (two : HalfBridgeFree (Before paths) 2) :
    laterNestedOppositeLinkSet paths ⊆ (oppositeLinkGraphOfHalfTwo paths two).edgeSet := by
  rintro _ ⟨inner,central,w,v,rfl,_,link,_⟩
  exact (oppositeLinkGraphOfHalfTwo paths two).mem_edgeSet.mpr ⟨inner,central,link⟩

/-- A nested reversal needs a central path with at least four vertices. -/
theorem laterNestedOppositeLinkSet_eq_empty_of_short (paths : Fin p → List V)
    (short : ∀ i, (paths i).length ≤ 3) : laterNestedOppositeLinkSet paths = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨inner,central,w,v,_,_,link,outer,_,_,u,z,uv,wz,_⟩
  have left := uv.2.2
  have middle := link.2.2.1.2.2
  have right := wz.2.2
  have last := List.idxOf_lt_length_of_mem wz.2.1
  have bound := short central
  omega

noncomputable def removeLaterNestedOppositeStarts (paths : Fin p → List V) (i : Fin p) : List V := by
  classical
  exact (paths i).filter fun w => decide (¬ ∃ (central : Fin p) (v : V), LaterNestedOppositeLink paths i central w v)

theorem removeLaterNestedOppositeStarts_mem {paths : Fin p → List V} {i : Fin p} {w : V} :
    w ∈ removeLaterNestedOppositeStarts paths i ↔ w ∈ paths i ∧
      ¬ ∃ (central : Fin p) (v : V), LaterNestedOppositeLink paths i central w v := by
  simp [removeLaterNestedOppositeStarts]

theorem removeLaterNestedOppositeStarts_sublist (paths : Fin p → List V) (i : Fin p) :
    (removeLaterNestedOppositeStarts paths i).Sublist (paths i) := by
  unfold removeLaterNestedOppositeStarts
  exact List.filter_sublist

private theorem reverse_link_chain_first {paths : Fin p → List V} {inner central : Fin p} {u w v : V}
    (links : Relation.TransGen (OppositeNeighbors paths inner central) w v)
    (left : Before paths central u v) :
    ∃ a, OppositeNeighbors paths inner central w a ∧ Before paths central u a := by
  induction links with
  | single pair => exact ⟨_,pair,left⟩
  | tail links last ih =>
    have reverse := last.2.2.1
    exact ih ⟨left.1,reverse.2.1,left.2.2.trans reverse.2.2⟩

/-- Deleting the starting incidences of these links removes all later
nested reversals, including when the inner reversal spans several links. -/
theorem removeLaterNestedOppositeStarts_no_later_nested {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (two : HalfBridgeFree (Before paths) 2) :
    NoLaterNestedOpposites (removeLaterNestedOppositeStarts paths) := by
  intro outer central inner outerCentral outerInner order u v w z uv vw wz zu wv
  have lift {i x y} (h : Before (removeLaterNestedOppositeStarts paths) i x y) : Before paths i x y :=
    listBefore_of_sublist (simple i) (removeLaterNestedOppositeStarts_sublist paths i) h
  have chain := oppositeNeighbors_connect_of_halfTwo two order.ne' (lift wv) (lift vw)
  obtain ⟨a,link,inside⟩ := reverse_link_chain_first chain (lift uv)
  exact (removeLaterNestedOppositeStarts_mem.mp wv.1).2
    ⟨central,a,order,link,outer,outerCentral,outerInner,u,z,inside,lift wz,lift zu⟩

private theorem link_owners_eq {paths : Fin p → List V} (two : HalfBridgeFree (Before paths) 2)
    {i j k l : Fin p} {w v : V} (one : OppositeNeighbors paths i j w v)
    (other : OppositeNeighbors paths k l w v) : i = k ∧ j = l := by
  constructor <;> by_contra different
  · exact no_parallel_list_steps two (by decide) different one.2.1 other.2.1
  · exact no_parallel_list_steps two (by decide) different one.2.2.1 other.2.2.1

variable [Fintype V]

/-- Distinct removed incidences charge distinct unordered links in the
restricted set. The earlier/later condition rules out swapped charges. -/
theorem removeLaterNestedOppositeStarts_mass {paths : Fin p → List V}
    (simple : ∀ i, (paths i).Nodup) (two : HalfBridgeFree (Before paths) 2) :
    (∑ i, (paths i).length) ≤ (∑ i, (removeLaterNestedOppositeStarts paths i).length) +
      Nat.card (laterNestedOppositeLinkSet paths) := by
  classical
  let kept := removeLaterNestedOppositeStarts paths
  let omitted := (univ : Finset (Fin p × V)).filter fun a => a.2 ∈ paths a.1 ∧ a.2 ∉ kept a.1
  have linked (a : omitted) : ∃ (central : Fin p) (v : V), LaterNestedOppositeLink paths a.val.1 central a.val.2 v := by
    obtain ⟨inside,absent⟩ := (mem_filter.mp a.property).2
    by_contra noLink
    exact absent (removeLaterNestedOppositeStarts_mem.mpr ⟨inside,noLink⟩)
  let central a := Classical.choose (linked a)
  let v a := Classical.choose (Classical.choose_spec (linked a))
  have witness (a : omitted) : LaterNestedOppositeLink paths a.val.1 (central a) a.val.2 (v a) :=
    Classical.choose_spec (Classical.choose_spec (linked a))
  let charge (a : omitted) : laterNestedOppositeLinkSet paths :=
    ⟨s(a.val.2,v a),a.val.1,central a,a.val.2,v a,rfl,witness a⟩
  have injective : Function.Injective charge := by
    intro a b same
    rcases Sym2.eq_iff.mp (congrArg Subtype.val same) with ⟨start,finish⟩ | ⟨start,finish⟩
    · have other : OppositeNeighbors paths b.val.1 (central b) a.val.2 (v a) :=
        (congrArg₂ (OppositeNeighbors paths b.val.1 (central b)) start finish).mpr (witness b).2.1
      exact Subtype.ext (Prod.ext (link_owners_eq two (witness a).2.1 other).1 start)
    · have other : OppositeNeighbors paths (central b) b.val.1 a.val.2 (v a) :=
        (congrArg₂ (OppositeNeighbors paths (central b) b.val.1) start finish).mpr
          (oppositeNeighbors_swap_of_halfTwo two (witness b).2.1)
      obtain ⟨sameInner,sameCentral⟩ := link_owners_eq two (witness a).2.1 other
      have backwards : b.val.1 < central b :=
        (congrArg₂ (fun i j : Fin p => i < j) sameCentral sameInner).mp (witness a).1
      exact (lt_asymm backwards (witness b).1).elim
  have loss : omitted.card ≤ Nat.card (laterNestedOppositeLinkSet paths) := by
    simpa only [Nat.card_eq_fintype_card (α := omitted),Fintype.card_coe] using
      Nat.card_le_card_of_injective charge injective
  have omittedSize : omitted.card = ∑ i, ((paths i).toFinset \ (kept i).toFinset).card := by
    unfold omitted
    rw [card_filter,← univ_product_univ,Finset.sum_product]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    congr 1
    ext v
    simp
  have exactMass : omitted.card + (∑ i, (kept i).length) = ∑ i, (paths i).length := by
    rw [omittedSize,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    let sub := removeLaterNestedOppositeStarts_sublist paths i
    have subset : (kept i).toFinset ⊆ (paths i).toFinset := fun _ mem => List.mem_toFinset.mpr (sub.subset (List.mem_toFinset.mp mem))
    rw [← List.toFinset_card_of_nodup (sub.nodup (simple i)),← List.toFinset_card_of_nodup (simple i),
      card_sdiff_add_card_eq_card subset]
  change (∑ i, (paths i).length) ≤ (∑ i, (kept i).length)+Nat.card (laterNestedOppositeLinkSet paths)
  omega

/-- The original frozen caps and both budgets need only a bound for the
links used by later nested reversals. -/
theorem regularization_list_frozen_half_four_of_few_nested_links {n : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 8*Nat.card (laterNestedOppositeLinkSet paths) ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let kept := removeLaterNestedOppositeStarts paths
  let K := ∑ i, (kept i).length
  have two : HalfBridgeFree (Before paths) 2 := fun _ h => free (h.trans (by decide))
  have sub (i : Fin p) := removeLaterNestedOppositeStarts_sublist paths i
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptFree : HalfBridgeFree (Before kept) 4 := by
    intro k limit bridge earlier
    exact free limit (bridge.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step)) earlier
  have loss : M ≤ K+Nat.card (laterNestedOppositeLinkSet paths) := removeLaterNestedOppositeStarts_mass simple two
  have enough : 7*M ≤ 8*K := by change 8*Nat.card (laterNestedOppositeLinkSet paths) ≤ M at few; omega
  have upper : K ≤ M := sum_le_sum fun i _ => (sub i).length_le
  have allowed : localOrderAdmissible true 4 (listRegularizedPaths kept (4*M/n) (4*M/p)) :=
    listRegularizedPaths_halfFree_of_no_later_nested keptSimple
      (removeLaterNestedOppositeStarts_no_later_nested simple two) keptFree (4*M/n) (4*M/p)
  exact regularization_list_frozen_of_seven_eighths_mass paths kept simple keptSimple free (by decide)
    hn hp dense long upper (fun _ => enough) allowed

end OnlineReachabilityPreservers
