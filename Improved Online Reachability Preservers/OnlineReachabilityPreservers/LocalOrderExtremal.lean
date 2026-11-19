import Mathlib.Data.Fintype.List
import OnlineReachabilityPreservers.CommonOrderExtremal
import OnlineReachabilityPreservers.LocalBalancedRegularization

/-! Choose a genuinely maximal locally ordered input for short-bridge cleaning. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem listBefore_of_sorted_finset {n p : ℕ} {paths : Fin p → Finset (Fin n)}
    {i : Fin p} {u v : Fin n} (step : ListBefore (fun a => (paths a).sort) i u v) :
    PathBefore paths i u v := by
  let L := (paths i).sort
  have uAt : L.idxOf u < L.length := List.idxOf_lt_length_of_mem step.1
  have vAt : L.idxOf v < L.length := List.idxOf_lt_length_of_mem step.2.1
  have ordered : L.Pairwise (· ≤ ·) := pairwise_sort _ _
  have less := List.pairwise_iff_getElem.mp ordered (L.idxOf u) (L.idxOf v) uAt vAt step.2.2
  rw [List.getElem_idxOf uAt, List.getElem_idxOf vAt] at less
  exact ⟨(mem_sort _).mp step.1, (mem_sort _).mp step.2.1, less.lt_of_ne (listBefore_ne step)⟩

/-- The two exclusion conditions on locally ordered families. -/
def localOrderAdmissible {V I : Type*} [DecidableEq V] [LinearOrder I]
    (half : Bool) (size : ℕ) (paths : I → List V) : Prop :=
  if half then HalfBridgeFree (ListBefore paths) size else BridgeFree (ListBefore paths) size

/-- For positive budgets, a finite maximum among all eligible simple
list families exists in each mode. Its mass is at least both budgets. -/
theorem localOrderExtremal_isDense (n p size : ℕ) (half : Bool) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half size paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half size other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      n ≤ ∑ i, (paths i).length ∧ p ≤ ∑ i, (paths i).length := by
  classical
  obtain ⟨common,allowedCommon,_,nCommon,pCommon⟩ := commonOrderExtremal_isDense n p size half hn hp
  let Family := Fin p → {path : List (Fin n) // path.Nodup}
  let : Fintype Family := inferInstanceAs (Fintype (Fin p → {path : List (Fin n) // path.Nodup}))
  let lists (f : Family) : Fin p → List (Fin n) := fun i => (f i).val
  let base : Family := fun i => ⟨(common i).sort, sort_nodup _ _⟩
  have allowed : localOrderAdmissible half size (lists base) := by
    cases half
    · intro k hk
      exact ⟨fun b => (allowedCommon hk).false (b.mapPaths id Function.injective_id
        (fun _ _ _ step => listBefore_of_sorted_finset step))⟩
    · intro k hk b earlier
      exact allowedCommon hk (b.mapPaths id Function.injective_id
        (fun _ _ _ step => listBefore_of_sorted_finset step)) earlier
  let choices := (univ : Finset Family).filter fun f => localOrderAdmissible half size (lists f)
  have contains : base ∈ choices := mem_filter.mpr ⟨mem_univ _,allowed⟩
  obtain ⟨best,inChoices,maximal⟩ := exists_max_image choices (fun f => ∑ i, (lists f i).length) ⟨base,contains⟩
  have nb : n ≤ ∑ i, (lists base i).length := by simpa only [lists,base,length_sort] using nCommon
  have pb : p ≤ ∑ i, (lists base i).length := by simpa only [lists,base,length_sort] using pCommon
  refine ⟨lists best,fun i => (best i).property,(mem_filter.mp inChoices).2,?_,
    nb.trans (maximal base contains),pb.trans (maximal base contains)⟩
  intro other simple legal
  let entry : Family := fun i => ⟨other i,simple i⟩
  exact maximal entry (mem_filter.mpr ⟨mem_univ _,legal⟩)

/-- Through size three, retain a constant fraction of the unrestricted
maximum and meet both budgets and all four original-average caps. -/
theorem localOrderExtremal_balanced_three (n p : ℕ) (half : Bool) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half 3 paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half 3 other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      let D := (4*M)/Fintype.card (Fin n)
      let L := (4*M)/Fintype.card (Fin p)
      let copies := splitListVertices paths D
      ∃ A : Finset (ListVertexBlockIndex paths D), ∃ B : Finset (ListBlockIndex copies L),
        let clean := restrictListPaths (listRegularizedPaths paths D L) A B
        A.card ≤ n ∧ B.card ≤ p ∧ localOrderAdmissible half 3 clean ∧
          M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
          (∀ v : A, (M:ℝ)/(4*(n:ℝ)) ≤ (occurrences (fun i => (clean i).toFinset) v).card ∧
            ((occurrences (fun i => (clean i).toFinset) v).card : ℝ) ≤ 4*(M:ℝ)/(n:ℝ)) ∧
          (∀ i : B, (M:ℝ)/(4*(p:ℝ)) ≤ (clean i).length ∧
            ((clean i).length : ℝ) ≤ 4*(M:ℝ)/(p:ℝ)) := by
  obtain ⟨paths,simple,eligible,maximal,nd,pd⟩ := localOrderExtremal_isDense n p 3 half hn hp
  obtain ⟨A,B,vertices,pathsCap,mass,upper,degree,length,halfFree,fullFree⟩ :=
    regularization_list_balanced_caps_three paths simple (by simpa using hn) (by simpa using hp)
      (by simpa using nd) (by simpa using pd)
  refine ⟨paths,simple,eligible,maximal,A,B,by simpa using vertices,by simpa using pathsCap,
    ?_,mass,upper,by simpa using degree,by simpa using length⟩
  cases half
  · exact fullFree eligible
  · exact halfFree eligible

end OnlineReachabilityPreservers
