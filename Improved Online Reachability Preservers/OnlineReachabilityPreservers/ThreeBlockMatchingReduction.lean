import OnlineReachabilityPreservers.FullThreeLongRows
import OnlineReachabilityPreservers.PositiveMatchingHalfRows

/-! Disjoint contiguous triples capture a fixed fraction of all long-row incidences. -/

namespace OnlineReachabilityPreservers

open Finset
open SimpleGraph.TripartiteFromTriangles
local notation "Before" => SourceAudit.BeforeIn

private theorem exists_complete_contiguous_triples {n p k : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : localOrderAdmissible half k paths) (three : 3 ≤ k) :
    ∃ pieces : Fin (∑ i, (paths i).length/3) → List (Fin n),
      (∀ i, (pieces i).Nodup ∧ (pieces i).length = 3) ∧ localOrderAdmissible half 3 pieces := by
  let width := 3
  let q := ∑ i, (paths i).length/width
  obtain ⟨full,lengths,remainders⟩ := splitListPaths_full_block_profile paths simple (L := width) (by decide)
  have countAll : Fintype.card (ListBlockIndex paths width) = q+p := by
    change Fintype.card (Σ i : Fin p, Fin (blockCount (paths i).toFinset width)) = q+p
    simp [Fintype.card_sigma,blockCount,List.toFinset_card_of_nodup (simple _),sum_add_distrib,q]
  have count : full.card = q := by
    rw [card_sdiff_of_subset (subset_univ full),card_univ,countAll,Fintype.card_fin] at remainders
    have fits : full.card ≤ q+p := (card_le_univ full).trans_eq countAll
    omega
  let enumerate := Fintype.orderIsoFinOfCardEq (↥full) ((Fintype.card_coe _).trans count)
  let block (i : Fin q) := (enumerate i).val
  let parent (i : Fin q) := (block i).fst
  let pieces (i : Fin q) := splitListPaths paths width (block i)
  have blockInjective : Function.Injective block := Subtype.val_injective.comp enumerate.injective
  have parentMono : Monotone parent := fun _ _ h =>
    block_parent_mono (fun i => (paths i).toFinset) width (enumerate.monotone h)
  have sub (i : Fin q) : (pieces i).Sublist (paths (parent i)) := List.filter_sublist
  have steps {i x y} (before : Before pieces i x y) : Before paths (parent i) x y :=
    listBefore_of_sublist (paths := fun j : Fin q => paths (parent j)) (simple (parent i)) (sub i) before
  have disjoint {i j x} (different : i ≠ j) (same : parent i = parent j)
      (first : x ∈ pieces i) (next : x ∈ pieces j) : False :=
    splitListPaths_disjoint (fun eq => different (blockInjective eq)) same first next
  refine ⟨pieces,fun i => ⟨(sub i).nodup (simple (parent i)),lengths (block i) (enumerate i).property⟩,?_⟩
  cases half
  · change BridgeFree (Before paths) k at free
    change BridgeFree (Before pieces) 3
    exact (show BridgeFree (Before paths) 3 from fun _ size => free (size.trans three)).split_list_paths_three
      parent (fun {_ _ _} => steps) (fun {_ _ _} => disjoint)
  · change HalfBridgeFree (Before paths) k at free
    change HalfBridgeFree (Before pieces) 3
    exact (show HalfBridgeFree (Before paths) 3 from fun _ size => free (size.trans three)).split_list_paths_three
      parent parentMono (fun {_ _ _} => steps) (fun {_ _ _} => disjoint)

private theorem long_mass_le_five_mul_complete_triples {V : Type*} {p : ℕ} (paths : Fin p → List V) :
    listMassAboveWidth paths 2 ≤ 5*(∑ i, (paths i).length/3) := by
  unfold listMassAboveWidth
  rw [sum_filter,mul_sum]
  apply sum_le_sum
  intro i _
  by_cases long : 2 < (paths i).length
  · rw [ite_eq_left long]
    omega
  · rw [ite_eq_right long]
    exact Nat.zero_le _

/-- The disjoint contiguous triples of all half-free rows together give
positive matching fibers on three copies of the original vertices. Their
count is at least one fifth of the original long-row mass. -/
theorem half_three_long_mass_positive_matchings {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    ∃ t : Finset (Fin n × Fin n × Fin n), t.card = (∑ i, (paths i).length/3) ∧
      listMassAboveWidth paths 2 ≤ 5*t.card ∧ ExplicitDisjoint t ∧
      ∃ (left right : Fin n → Fin n → ℝ),
        ∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t) := by
  obtain ⟨pieces,properties,legal⟩ := exists_complete_contiguous_triples (half := true) paths simple free three
  obtain ⟨t,count,disjoint,positive⟩ := first_three_vertices_positive_matchings pieces
    (fun i => (properties i).1) legal le_rfl
  have exactCount : t.card = ∑ i, (paths i).length/3 := by
    simpa only [(fun i => (properties i).2),show 2 < (3:ℕ) by decide,filter_true,card_univ,Fintype.card_fin] using count
  exact ⟨t,exactCount,exactCount ▸ long_mass_le_five_mul_complete_triples paths,disjoint,positive⟩

/-- The analogous reduction for full-three exclusion yields edge-disjoint
triangles with no accidental triangle, in the Ruzsa–Szemerédi setting. -/
theorem full_three_long_mass_induced_matching_triangles {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (three : 3 ≤ k) :
    ∃ t : Finset (Fin n × Fin n × Fin n), t.card = (∑ i, (paths i).length/3) ∧
      listMassAboveWidth paths 2 ≤ 5*t.card ∧ ExplicitDisjoint t ∧ NoAccidental t := by
  obtain ⟨pieces,properties,legal⟩ := exists_complete_contiguous_triples (half := false) paths simple free three
  obtain ⟨t,count,disjoint,noAccidental⟩ := first_three_vertices_tripartite_triangles pieces
    (fun i => (properties i).1) legal le_rfl
  have exactCount : t.card = ∑ i, (paths i).length/3 := by
    simpa only [(fun i => (properties i).2),show 2 < (3:ℕ) by decide,filter_true,card_univ,Fintype.card_fin] using count
  exact ⟨t,exactCount,exactCount ▸ long_mass_le_five_mul_complete_triples paths,disjoint,noAccidental⟩

private theorem third_matching_card_le {n : ℕ} (t : Finset (Fin n × Fin n × Fin n))
    [ExplicitDisjoint t] (c : Fin n) : (t.filter (fun x => x.2.2 = c)).card ≤ n := calc
  _ ≤ (univ : Finset (Fin n)).card := by
    apply card_le_card_of_injOn (fun x => x.1)
    · intro x _
      exact mem_univ _
    · rintro ⟨a,b,u⟩ first ⟨a',b',v⟩ next (rfl : a = a')
      have firstOn : (a,b,u) ∈ t := (mem_filter.mp first).1
      have nextOn : (a,b',v) ∈ t := (mem_filter.mp next).1
      have uEq : u = c := (mem_filter.mp first).2
      have vEq : v = c := (mem_filter.mp next).2
      subst u
      subst v
      obtain rfl := ExplicitDisjoint.inj₁ (t := t) firstOn nextOn
      rfl
  _ = _ := by simp

/-- A quadratic number of triples forces linearly many final-coordinate
fibers of linear size. Coordinate-pair uniqueness makes each a matching. -/
theorem many_large_third_matching_fibers {n : ℕ} (t : Finset (Fin n × Fin n × Fin n))
    [ExplicitDisjoint t] (δ : ℝ) (nonnegative : 0 ≤ δ) (dense : 2*δ*(n:ℝ)^2 ≤ t.card) :
    δ*(n:ℝ) ≤ ((univ.filter (fun c => δ*(n:ℝ) ≤ ((t.filter (fun x => x.2.2 = c)).card:ℝ))).card:ℝ) := by
  let fiber (c : Fin n) := t.filter (fun x => x.2.2 = c)
  let large := univ.filter (fun c : Fin n => δ*(n:ℝ) ≤ ((fiber c).card:ℝ))
  change δ*(n:ℝ) ≤ (large.card:ℝ)
  by_cases hn : 0 < n
  swap
  · have n0 : (n:ℝ) = 0 := by exact_mod_cast (show n = 0 by omega)
    rw [n0,mul_zero]
    positivity
  have total : (t.card:ℝ) = ∑ c, ((fiber c).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_fiberwise (s := t) (t := (univ : Finset (Fin n)))
      (f := fun x => x.2.2) (fun x _ => mem_univ x.2.2)
  have big : (∑ c ∈ large, ((fiber c).card:ℝ)) ≤ (large.card:ℝ)*(n:ℝ) := calc
    _ ≤ ∑ _c ∈ large, (n:ℝ) := sum_le_sum fun c _ => Nat.cast_le.mpr (third_matching_card_le t c)
    _ = _ := by simp [nsmul_eq_mul]
  have small : (∑ c ∈ largeᶜ, ((fiber c).card:ℝ)) ≤ δ*(n:ℝ)^2 := calc
    _ ≤ ∑ _c ∈ largeᶜ, δ*(n:ℝ) := sum_le_sum fun c outside => by
      have missed : ¬ δ*(n:ℝ) ≤ ((fiber c).card:ℝ) := fun fits => (mem_compl.mp outside) (mem_filter.mpr ⟨mem_univ _,fits⟩)
      exact (lt_of_not_ge missed).le
    _ = ((largeᶜ : Finset (Fin n)).card:ℝ)*(δ*(n:ℝ)) := by simp [nsmul_eq_mul]
    _ ≤ (n:ℝ)*(δ*(n:ℝ)) := mul_le_mul_of_nonneg_right (by simpa using card_le_univ (largeᶜ : Finset (Fin n))) (by positivity)
    _ = _ := by ring
  rw [← sum_add_sum_compl large] at total
  have nPos : (0:ℝ) < n := by exact_mod_cast hn
  apply (mul_le_mul_iff_right₀ nPos).mp
  nlinarith only [total,big,small,dense]

/-- Quadratic mass and a starting mean length above eight on the half
side require linearly many linear-size positive matchings. This supplies
a necessary condition for the conditional comparison obstruction. -/
theorem dense_high_mean_half_gives_many_large_positive_matchings {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k)
    (three : 3 ≤ k) (η : ℝ) (positive : 0 < η)
    (high : 8*p < ∑ i, (paths i).length) (dense : η*(n:ℝ)^2 ≤ ((∑ i, (paths i).length : ℕ):ℝ)) :
    ∃ t : Finset (Fin n × Fin n × Fin n), ExplicitDisjoint t ∧
      (η/8)*(n:ℝ) ≤ ((univ.filter (fun c => (η/8)*(n:ℝ) ≤ ((t.filter (fun x => x.2.2 = c)).card:ℝ))).card:ℝ) ∧
      ∃ (left right : Fin n → Fin n → ℝ),
        ∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t) := by
  obtain ⟨t,count,_,disjoint,weights⟩ := half_three_long_mass_positive_matchings paths simple free three
  let : ExplicitDisjoint t := disjoint
  let M := ∑ i, (paths i).length
  have mass : M ≤ 3*t.card+2*p := calc
    _ ≤ ∑ i, (3*((paths i).length/3)+2) := sum_le_sum (fun i _ => by omega)
    _ = _ := by
      rw [sum_add_distrib,← mul_sum,← count]
      simp [Nat.mul_comm p 2]
  have hR : (8:ℝ)*p < (M:ℝ) := by exact_mod_cast high
  have mR : (M:ℝ) ≤ 3*(t.card:ℝ)+2*(p:ℝ) := by exact_mod_cast mass
  have dR : η*(n:ℝ)^2 ≤ (M:ℝ) := dense
  have tR : 2*(η/8)*(n:ℝ)^2 ≤ (t.card:ℝ) := by nlinarith only [hR,mR,dR]
  exact ⟨t,disjoint,many_large_third_matching_fibers t _ (by positivity) tR,weights⟩

end OnlineReachabilityPreservers
