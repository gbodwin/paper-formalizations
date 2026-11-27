import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.FrozenFullReturnSupportedCover
import OnlineReachabilityPreservers.OutputAverageDistinctCleaning

/-! Restrict one budget to a finite cutoff before using all-size full exclusion. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

private theorem mask_sublist {n p : ℕ} (paths : Fin p → List (Fin n))
    (A : Finset (Fin n)) (B : Finset (Fin p)) (i : Fin p) :
    (listPiecesInRectangle paths A B i).Sublist (paths i) := by
  unfold listPiecesInRectangle
  split
  · exact List.filter_sublist
  · exact List.nil_sublist _

private theorem mask_membership {n p : ℕ} {paths : Fin p → List (Fin n)}
    {A : Finset (Fin n)} {B : Finset (Fin p)} {i : Fin p} {v : Fin n}
    (member : v ∈ listPiecesInRectangle paths A B i) : i ∈ B ∧ v ∈ A := by
  by_cases active : i ∈ B
  · have both : v ∈ paths i ∧ v ∈ A := by
      simpa [listPiecesInRectangle,active] using member
    exact ⟨active,both.2⟩
  · simp [listPiecesInRectangle,active] at member

/-- With one support at most the input cutoff, the masked rows exclude
full bridges of every size. Row labels and original comparisons stay fixed. -/
theorem fullBridgeFree_all_mask_of_small_support {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (A : Finset (Fin n)) (B : Finset (Fin p))
    (bounded : min A.card B.card ≤ cutoff) (d : ℕ) :
    IsEmpty (Bridge (Before (listPiecesInRectangle paths A B)) d) := by
  let kept := listPiecesInRectangle paths A B
  refine ⟨fun bridge => ?_⟩
  have arcRow (i : Fin (d+1)) : bridge.arc i ∈ B := (mask_membership (bridge.arcStep i).1).1
  have riverRow : bridge.river ∈ B := (mask_membership bridge.riverStep.1).1
  have inA (j : Fin (d+2)) : bridge.vertex j ∈ A :=
    Fin.lastCases (mask_membership bridge.riverStep.2.1).2
      (fun i => (mask_membership (bridge.arcStep i).1).2) j
  let v (j : Fin (d+2)) : A := ⟨bridge.vertex j,inA j⟩
  have vertices : d+2 ≤ A.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using
      Fintype.card_le_of_injective v (fun i j equal => bridge.distinctVertices (congrArg Subtype.val equal))
  let indexed : Bridge (fun (i : B) => Before kept i.val) d :=
    ⟨bridge.vertex,(fun i => ⟨bridge.arc i,arcRow i⟩),⟨bridge.river,riverRow⟩,
      bridge.distinctVertices,(fun i j equal => bridge.distinctArcs (congrArg Subtype.val equal)),
      (fun i equal => bridge.river_ne_arc i (congrArg Subtype.val equal)),bridge.riverStep,bridge.arcStep⟩
  have rows : d+2 ≤ B.card := by simpa only [Fintype.card_coe] using SourceAudit.bridge_path_count_le indexed
  exact (free ((le_min vertices rows).trans bounded)).false (bridge.mapPaths id Function.injective_id
    (fun i _ _ step => listBefore_of_sublist (simple i) (mask_sublist paths A B i) step))

private theorem mask_mass_vertices {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (A : Finset (Fin n)) :
    (∑ i, (listPiecesInRectangle paths A univ i).length) =
      ∑ v ∈ A, (occurrences (fun i => (paths i).toFinset) v).card := by
  let kept := listPiecesInRectangle paths A univ
  have keptSet (i : Fin p) : (kept i).toFinset = (paths i).toFinset ∩ A := by
    ext v
    simp [kept,listPiecesInRectangle]
  have keptCount (v : Fin n) : (occurrences (fun i => (kept i).toFinset) v).card =
      if v ∈ A then (occurrences (fun i => (paths i).toFinset) v).card else 0 := by
    by_cases inside : v ∈ A <;> simp [occurrences,keptSet,inside]
  calc
    _ = ∑ i, (kept i).toFinset.card := sum_congr rfl (fun i _ =>
      (List.toFinset_card_of_nodup ((mask_sublist paths A univ i).nodup (simple i))).symm)
    _ = ∑ v, (occurrences (fun i => (kept i).toFinset) v).card := (sum_occurrences _).symm
    _ = ∑ v, (if v ∈ A then (occurrences (fun i => (paths i).toFinset) v).card else 0) :=
      sum_congr rfl (fun v _ => keptCount v)
    _ = _ := by rw [← sum_filter]; simp

private theorem mask_mass_rows {n p : ℕ} (paths : Fin p → List (Fin n)) (B : Finset (Fin p)) :
    (∑ i, (listPiecesInRectangle paths univ B i).length) = ∑ i ∈ B, (paths i).length := by
  calc
    _ = ∑ i, (if i ∈ B then (paths i).length else 0) := by
      refine sum_congr rfl fun i _ => ?_
      by_cases active : i ∈ B <;> simp [listPiecesInRectangle,active]
    _ = _ := by rw [← sum_filter]; simp

/-- Restrict the smaller support to the cutoff. A fraction `a / b` of
that support suffices to keep at least this fraction of the incidences,
now in a family excluding full bridges of all sizes. -/
theorem fullBridgeFree_subrows_mass_of_cutoff_ratio {n p cutoff a b : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (ratio : a ≤ b) (near : a*min n p ≤ b*cutoff) :
    ∃ kept : Fin p → List (Fin n), (∀ i, (kept i).Sublist (paths i)) ∧
      (∀ d, IsEmpty (Bridge (Before kept) d)) ∧ a*(∑ i, (paths i).length) ≤ b*(∑ i, (kept i).length) := by
  by_cases vertices : n ≤ p
  · let degree (v : Fin n) := (occurrences (fun i => (paths i).toFinset) v).card
    have total : ∑ v, degree v = ∑ i, (paths i).length := by
      unfold degree
      rw [sum_occurrences]
      exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
    have fits : a*(univ : Finset (Fin n)).card ≤ b*cutoff := by
      simpa only [min_eq_left vertices,card_univ,Fintype.card_fin] using near
    obtain ⟨A,_,size,retained⟩ := trim_weights_ratio univ degree ratio fits
    refine ⟨listPiecesInRectangle paths A univ,mask_sublist paths A univ,
      fullBridgeFree_all_mask_of_small_support paths simple free A univ ((min_le_left _ _).trans size),?_⟩
    rw [← total,mask_mass_vertices paths simple A]
    exact retained
  · have fits : a*(univ : Finset (Fin p)).card ≤ b*cutoff := by
      simpa only [min_eq_right (le_of_not_ge vertices),card_univ,Fintype.card_fin] using near
    obtain ⟨B,_,size,retained⟩ := trim_weights_ratio univ (fun i => (paths i).length) ratio fits
    refine ⟨listPiecesInRectangle paths univ B,mask_sublist paths univ B,
      fullBridgeFree_all_mask_of_small_support paths simple free univ B ((min_le_right _ _).trans size),?_⟩
    rw [mask_mass_rows]
    exact retained

/-- A full cutoff at least 27/28 of the smaller original budget admits
frozen cleaning at that cutoff. No hypothesis on the precedence
components or the choice of a return cover is needed. -/
theorem regularization_list_frozen_full_of_near_cutoff {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (near : 27*min n p ≤ 28*cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 128*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨kept,sub,all,retained⟩ := fullBridgeFree_subrows_mass_of_cutoff_ratio paths simple free (by decide : 27 ≤ 28) near
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  exact regularization_list_frozen_full_of_component_fullFree_after_deletions paths kept simple sub free
    (precedenceComponent_fullFree keptSimple all) two hn hp dense long retained

/-- The near-cutoff witness can have literal distinct nonempty rows. -/
theorem regularization_list_frozen_full_distinct_of_near_cutoff {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (two : 2 ≤ cutoff) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (near : 27*min n p ≤ 28*cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 128*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 128)
    paths distinct nonempty simple free two hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_of_near_cutoff paths simple free two hn hp dense long near)

/-- The frozen near-cutoff bound at the unrestricted indexed maximum. -/
theorem localOrderExtremal_frozen_full_of_near_cutoff (n p cutoff : ℕ)
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (near : 27*min n p ≤ 28*cutoff) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
        M ≤ 128*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p cutoff false hn hp
  exact ⟨paths,simple,free,maximal,
    regularization_list_frozen_full_of_near_cutoff paths simple free two hn hp dense long near⟩

/-- The frozen near-cutoff bound at the feasible literal maximum. -/
theorem localOrderDistinctExtremal_frozen_full_of_near_cutoff {n p cutoff : ℕ}
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (near : 27*min n p ≤ 28*cutoff)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
        BridgeFree (Before clean) cutoff ∧ M ≤ 128*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,distinct,rows,free,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense false hp feasible
  exact ⟨paths,distinct,rows,free,maximal,regularization_list_frozen_full_distinct_of_near_cutoff paths
    distinct (fun i => (rows i).1) (fun i => (rows i).2) free two hn hp dense near⟩

/-- A cutoff at a `1 / C` fraction of the smaller budget suffices for
the four output-average caps. The indexed witness excludes every full
bridge, and the loss factor is linear in `C`. -/
theorem regularization_list_output_average_full_of_cutoff_ratio {n p cutoff C : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (positive : 0 < C) (near : min n p ≤ C*cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before clean) d)) ∧
      M ≤ (523*C)*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  by_cases small : M ≤ C*max n p
  · obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,kept,within,caps⟩ :=
      regularization_list_output_average_of_linear_mass (M := max n p) (k := p) false hn hp
        (le_max_left _ _) (le_max_right _ _) (by omega)
    have enough : M ≤ (523*C)*(∑ i, (clean i).length) := calc
      _ ≤ C*max n p := small
      _ ≤ C*(392*(∑ i, (clean i).length)) := Nat.mul_le_mul_left _ kept
      _ = (392*C)*(∑ i, (clean i).length) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,
      bridgeFree_all_of_cutoff_ge_min cleanFree ((min_le_right _ _).trans qFits),
      enough,within.trans (max_le dense long),caps⟩
  obtain ⟨kept,sub,all,retained⟩ := fullBridgeFree_subrows_mass_of_cutoff_ratio paths simple free
    (show 1 ≤ C by omega) (by simpa only [Nat.one_mul] using near)
  let K := ∑ i, (kept i).length
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have lower : M ≤ C*K := by simpa only [Nat.one_mul] using retained
  have fills : max n p ≤ K := by
    apply Nat.le_of_mul_le_mul_left (c := C) _ positive
    exact (Nat.lt_of_not_ge small).le.trans lower
  have upper : K ≤ M := sum_le_sum fun i _ => (sub i).length_le
  obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,mass,within,caps⟩ :=
    regularization_list_output_average_full_all kept keptSimple all hn hp
      ((le_max_left _ _).trans fills) ((le_max_right _ _).trans fills)
  have enough : M ≤ (523*C)*(∑ i, (clean i).length) := calc
    _ ≤ C*K := lower
    _ ≤ C*(523*(∑ i, (clean i).length)) := Nat.mul_le_mul_left _ mass
    _ = _ := by ring
  exact ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,enough,within.trans upper,caps⟩

/-- With literal nonempty distinct input, a constant cutoff fraction
gives an output-average witness with nonempty distinct rows as well. -/
theorem regularization_list_output_average_full_distinct_of_cutoff_ratio {n p cutoff C : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff) (positive : 0 < C) (near : min n p ≤ C*cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ (18*(523*C))*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean :=
  regularization_list_output_average_distinct_of_indexed_with_retention (half := false)
    paths distinct nonempty simple free two hn hp dense (fun long => by
      obtain ⟨v,vFits,q,qFits,clean,cleanSimple,all,kept,within,caps⟩ :=
        regularization_list_output_average_full_of_cutoff_ratio paths simple free positive near hn hp dense long
      exact ⟨v,vFits,q,qFits,clean,cleanSimple,fun d _ => all d,kept,within,caps⟩)

/-- Output-average cleaning at a constant cutoff fraction of the
unrestricted indexed maximum. -/
theorem localOrderExtremal_output_average_full_of_cutoff_ratio (n p cutoff C : ℕ)
    (hn : 0 < n) (hp : 0 < p) (positive : 0 < C) (near : min n p ≤ C*cutoff) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before clean) d)) ∧
        M ≤ (523*C)*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p cutoff false hn hp
  exact ⟨paths,simple,free,maximal,
    regularization_list_output_average_full_of_cutoff_ratio paths simple free positive near hn hp dense long⟩

/-- Output-average cleaning at the feasible literal maximum under the
same cutoff fraction. -/
theorem localOrderDistinctExtremal_output_average_full_of_cutoff_ratio {n p cutoff C : ℕ}
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (positive : 0 < C) (near : min n p ≤ C*cutoff)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
        BridgeFree (Before clean) cutoff ∧ M ≤ (18*(523*C))*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,distinct,rows,free,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense false hp feasible
  exact ⟨paths,distinct,rows,free,maximal,regularization_list_output_average_full_distinct_of_cutoff_ratio paths
    distinct (fun i => (rows i).1) (fun i => (rows i).2) free two positive near hn hp dense⟩

/-- A constant cutoff fraction also gives a distinct nonempty
output-average witness excluding full bridges of every size. -/
theorem regularization_list_output_average_full_distinct_all_of_cutoff_ratio {n p cutoff C : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff) (positive : 0 < C) (near : min n p ≤ C*cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      (∀ d, IsEmpty (Bridge (Before clean) d)) ∧ M ≤ (18*(523*C))*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  let outputCutoff := max 2 p
  have long : p ≤ M := by
    calc
      _ = ∑ i : Fin p, (1:ℕ) := by simp
      _ ≤ _ := sum_le_sum fun i _ => List.length_pos_of_ne_nil (nonempty i)
  have pCap := distinctPathCount_le_square paths distinct nonempty simple two free.halfFree
  have indexed : ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) outputCutoff ∧
      M ≤ (523*C)*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
    obtain ⟨v,vFits,q,qFits,clean,cleanSimple,all,kept,within,caps⟩ :=
      regularization_list_output_average_full_of_cutoff_ratio paths simple free positive near hn hp dense long
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,fun d _ => all d,kept,within,caps⟩
  obtain ⟨v,vFits,q,qFits,clean,injective,present,cleanSimple,cleanFree,keeps,within,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed_budget (half := false) (k := outputCutoff)
      (retention := 523*C) (le_max_left _ _) hn hp dense long pCap indexed
  exact ⟨v,vFits,q,qFits,clean,injective,present,cleanSimple,
    bridgeFree_all_of_cutoff_ge_min cleanFree ((min_le_right _ _).trans (qFits.trans (le_max_right _ _))),
    keeps,within,caps⟩

/-- The feasible literal maximum has an all-size full witness under
its own average caps at every fixed positive cutoff fraction. -/
theorem localOrderDistinctExtremal_output_average_full_all_of_cutoff_ratio {n p cutoff C : ℕ}
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (positive : 0 < C) (near : min n p ≤ C*cutoff)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
        (∀ d, IsEmpty (Bridge (Before clean) d)) ∧ M ≤ (18*(523*C))*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,distinct,rows,free,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense false hp feasible
  exact ⟨paths,distinct,rows,free,maximal,regularization_list_output_average_full_distinct_all_of_cutoff_ratio paths
    distinct (fun i => (rows i).1) (fun i => (rows i).2) free two positive near hn hp dense⟩

/-- With indexed rows, the all-size extremal mass is between the
finite-cutoff mass and that mass times the fraction of the smaller
budget covered by the cutoff. -/
theorem indexed_full_extrema_compare_all_sizes (n p cutoff : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ finite all : Fin p → List (Fin n),
      (∀ i, (finite i).Nodup) ∧ BridgeFree (Before finite) cutoff ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (finite i).length) ∧
      (∀ i, (all i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before all) d)) ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → (∀ d, IsEmpty (Bridge (Before other) d)) →
        (∑ i, (other i).length) ≤ ∑ i, (all i).length) ∧
      min cutoff (min n p)*(∑ i, (finite i).length) ≤ min n p*(∑ i, (all i).length) ∧
      (∑ i, (all i).length) ≤ ∑ i, (finite i).length := by
  let q := min n p
  obtain ⟨finite,simple,free,maximal,_,_⟩ := localOrderExtremal_isDense n p cutoff false hn hp
  obtain ⟨all,allSimple,allFinite,allMax,_,_⟩ := localOrderExtremal_isDense n p q false hn hp
  have allFree := bridgeFree_all_of_cutoff_ge_min allFinite (le_refl q)
  have fits : min cutoff q*q ≤ q*cutoff := by
    rw [Nat.mul_comm (min cutoff q)]
    exact Nat.mul_le_mul_left _ (min_le_left _ _)
  obtain ⟨kept,sub,keptAll,weighted⟩ := fullBridgeFree_subrows_mass_of_cutoff_ratio finite simple free
    (min_le_right cutoff q) fits
  have below : (∑ i, (kept i).length) ≤ ∑ i, (all i).length :=
    allMax kept (fun i => (sub i).nodup (simple i)) (fun d _ => keptAll d)
  exact ⟨finite,all,simple,free,maximal,allSimple,allFree,
    fun other otherSimple freeEvery => allMax other otherSimple (fun d _ => freeEvery d),
    weighted.trans (Nat.mul_le_mul_left _ below),maximal all allSimple (fun d _ => allFree d)⟩

end OnlineReachabilityPreservers
