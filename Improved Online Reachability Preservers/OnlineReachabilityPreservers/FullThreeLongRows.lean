import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import OnlineReachabilityPreservers.FrozenOverlongPaths
import OnlineReachabilityPreservers.FrozenSmallBudgets

/-! Full-three exclusion bounds the incidence mass of rows of length at least three. -/

namespace OnlineReachabilityPreservers

open Finset
open SimpleGraph.TripartiteFromTriangles
local notation "Before" => SourceAudit.BeforeIn

private abbrev longRows {n p : ℕ} (paths : Fin p → List (Fin n)) : Finset (Fin p) :=
  univ.filter (fun i => 2 < (paths i).length)

/-- The first three vertices of each long row define edge-disjoint
tripartite triangles, and full-three exclusion rules out mixed triangles. -/
theorem first_three_vertices_tripartite_triangles {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (three : 3 ≤ k) :
    ∃ t : Finset (Fin n × Fin n × Fin n), t.card = (univ.filter (fun i => 2 < (paths i).length)).card ∧
      ExplicitDisjoint t ∧ NoAccidental t := by
  classical
  let S := longRows paths
  have long (i : S) : 2 < (paths i.val).length := (mem_filter.mp i.property).2
  let v (i : S) (j : Fin 3) : Fin n := (paths i.val)[j.val]'(by have := j.isLt; have := long i; omega)
  let triple (i : S) : Fin n × Fin n × Fin n := (v i 0,v i 1,v i 2)
  let t := (univ : Finset S).image triple
  have step (i : S) {a b : Fin 3} (earlier : a < b) : Before paths i.val (v i a) (v i b) := by
    refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
    dsimp only [v]
    rw [(simple i.val).idxOf_getElem,(simple i.val).idxOf_getElem]
    exact earlier
  have sameRow {i j : S} {a b : Fin n} (first : Before paths i.val a b) (second : Before paths j.val a b) : i = j := by
    by_contra apart
    exact no_parallel_list_steps free.halfFree (by omega) (fun same => apart (Subtype.ext same)) first second
  have compare {i : S} {a b c : Fin n} (atTriple : triple i = (a,b,c)) :
      Before paths i.val a b ∧ Before paths i.val a c ∧ Before paths i.val b c := by
    obtain ⟨aEq,bc⟩ := Prod.mk.inj atTriple
    obtain ⟨bEq,cEq⟩ := Prod.mk.inj bc
    exact ⟨aEq ▸ bEq ▸ step i (by decide : (0:Fin 3) < 1),
      aEq ▸ cEq ▸ step i (by decide : (0:Fin 3) < 2),
      bEq ▸ cEq ▸ step i (by decide : (1:Fin 3) < 2)⟩
  have gives {a b c : Fin n} (member : (a,b,c) ∈ t) : ∃ i : S, triple i = (a,b,c) := by
    obtain ⟨i,_,equal⟩ := mem_image.mp member
    exact ⟨i,equal⟩
  have unique : Function.Injective triple := by
    intro i j equal
    exact sameRow (compare (rfl : triple i = (v i 0,v i 1,v i 2))).1 (compare equal.symm).1
  have count : t.card = S.card := by
    rw [show t = univ.image triple from rfl,card_image_of_injective _ unique,card_univ,Fintype.card_coe]
  have disjoint : ExplicitDisjoint t := by
    constructor
    · intro a b c a' old next
      obtain ⟨i,first⟩ := gives old
      obtain ⟨j,last⟩ := gives next
      have owner := sameRow (compare first).2.2 (compare last).2.2
      exact congrArg Prod.fst (first.symm.trans ((congrArg triple owner).trans last))
    · intro a b c b' old next
      obtain ⟨i,first⟩ := gives old
      obtain ⟨j,last⟩ := gives next
      have owner := sameRow (compare first).2.1 (compare last).2.1
      exact congrArg (fun z : Fin n × Fin n × Fin n => z.2.1) (first.symm.trans ((congrArg triple owner).trans last))
    · intro a b c c' old next
      obtain ⟨i,first⟩ := gives old
      obtain ⟨j,last⟩ := gives next
      have owner := sameRow (compare first).1 (compare last).1
      exact congrArg (fun z : Fin n × Fin n × Fin n => z.2.2) (first.symm.trans ((congrArg triple owner).trans last))
  have noAccidental : NoAccidental t := by
    constructor
    intro a a' b b' c c' bc ac ab
    obtain ⟨first,firstEq⟩ := gives ab
    obtain ⟨last,lastEq⟩ := gives bc
    obtain ⟨river,riverEq⟩ := gives ac
    by_cases equal : first.val = last.val
    · exact Or.inl (congrArg Prod.fst (firstEq.symm.trans ((congrArg triple (Subtype.ext equal)).trans lastEq)))
    by_cases equalRiver : river.val = first.val
    · exact Or.inr (Or.inl (congrArg (fun z : Fin n × Fin n × Fin n => z.2.1)
        (firstEq.symm.trans ((congrArg triple (Subtype.ext equalRiver.symm)).trans riverEq))))
    by_cases equalLast : river.val = last.val
    · exact Or.inl (congrArg Prod.fst (riverEq.symm.trans ((congrArg triple (Subtype.ext equalLast)).trans lastEq)))
    exact ((free three).false (threeListBridge equal equalRiver equalLast
      (compare firstEq).1 (compare lastEq).2.2 (compare riverEq).2.1)).elim
  exact ⟨t,count,disjoint,noAccidental⟩

/-- For any density threshold, sufficiently large full-three-free
vertex budgets have fewer long rows than that fraction of `n^2`.
The threshold on `n` does not depend on the row budget or cutoff. -/
theorem full_three_long_row_count_subquadratic (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      ((univ.filter (fun i => 2 < (paths i).length)).card:ℝ) ≤ ε*(n:ℝ)^2 := by
  let δ := SimpleGraph.triangleRemovalBound (ε/9)
  have δPos : 0 < δ := SimpleGraph.triangleRemovalBound_pos (by positivity)
  refine ⟨⌈1/δ⌉₊+1,?_⟩
  intro n p k large three paths simple free
  obtain ⟨t,count,disjoint,noAccidental⟩ := first_three_vertices_tripartite_triangles paths simple free three
  let : ExplicitDisjoint t := disjoint
  let : NoAccidental t := noAccidental
  rw [← count]
  by_contra! tooMany
  have dense : (ε/9)*((Fintype.card (Fin n)+Fintype.card (Fin n)+Fintype.card (Fin n))^2:ℕ) ≤ t.card := by
    simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_add]
    convert tooMany.le using 1
    ring
  have lower := (farFromTriangleFree (t := t) (𝕜 := ℝ) dense).le_card_cliqueFinset
  simp only [card_triangles,Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at lower
  have lower' : δ*(3*(n:ℝ))^3 ≤ (t.card:ℝ) := by
    convert lower using 1
    ring
  let firstTwo (x : t) : Fin n × Fin n := (x.val.1,x.val.2.1)
  have injective : Function.Injective firstTwo := by
    rintro ⟨⟨a,b,c⟩,x⟩ ⟨⟨a',b',c'⟩,y⟩ equal
    change (a,b) = (a',b') at equal
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    have ends := disjoint.inj₂ x y
    subst c'
    rfl
  have cap : t.card ≤ n^2 := by
    simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,pow_two] using
      Fintype.card_le_of_injective firstTwo injective
  have nPos : 0 < n := by omega
  have nReal : (0:ℝ) < n := by exact_mod_cast nPos
  have nLarge : 1/δ < (n:ℝ) := (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr (by omega))
  have δn : 1 < δ*(n:ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ δPos).mp nLarge
  have tooSmall : (n:ℝ)^2 < δ*(3*(n:ℝ))^3 := by
    calc
      _ < (δ*(n:ℝ))*(n:ℝ)^2 := lt_mul_of_one_lt_left (by positivity) δn
      _ = δ*(n:ℝ)^3 := by ring
      _ ≤ _ := by gcongr; linarith only [nReal]
  exact (not_lt_of_ge ((show (t.card:ℝ) ≤ (n:ℝ)^2 by exact_mod_cast cap))) (tooSmall.trans_le lower')

private theorem full_three_long_row_square_sum {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (two : 2 ≤ k) :
    (∑ i ∈ longRows paths, (paths i).length^2) ≤ 3*n^2 := by
  let S := longRows paths
  let masked (i : Fin p) := if 2 < (paths i).length then paths i else []
  have sub (i : Fin p) : (masked i).Sublist (paths i) := by
    by_cases long : 2 < (paths i).length
    · simp [masked,long]
    · simp [masked,long]
  have maskedFree : BridgeFree (Before masked) k := fun d limit =>
    ⟨fun b => (free limit).false (b.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step))⟩
  have moment := listLength_square_sum_le_halfTwo masked (fun i => (sub i).nodup (simple i)) maskedFree.halfFree two
  let total := ∑ i, (masked i).length
  let squares := ∑ i, (masked i).length^2
  have enough : 3*total ≤ squares := by
    dsimp only [total,squares]
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    by_cases long : 2 < (paths i).length
    · simpa only [masked,ite_eq_left long,pow_two] using
        (Nat.mul_le_mul_right (paths i).length (show 3 ≤ (paths i).length by omega))
    · simp [masked,long]
  change squares ≤ 2*(n*n-n)+total at moment
  have bound : squares ≤ 3*n^2 := by
    rw [pow_two]
    omega
  have weight : (∑ i ∈ S, (paths i).length^2) = squares := by
    dsimp only [S,longRows,squares]
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases long : 2 < (paths i).length <;> simp [masked,long]
  exact weight.le.trans bound

/-- The total mass of the rows of length at least three is `o(n^2)`
under full exclusion through size three, uniformly in the row budget
and every larger full cutoff. -/
theorem full_three_long_mass_subquadratic (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      (listMassAboveWidth paths 2 : ℝ) ≤ ε*(n:ℝ)^2 := by
  obtain ⟨N,small⟩ := full_three_long_row_count_subquadratic (ε^2/3) (by positivity)
  refine ⟨N,?_⟩
  intro n p k large three paths simple free
  let S := longRows paths
  let M := listMassAboveWidth paths 2
  let Q := ∑ i ∈ S, (paths i).length^2
  have number : (S.card:ℝ) ≤ (ε^2/3)*(n:ℝ)^2 := small large three paths simple free
  have squares : Q ≤ 3*n^2 := full_three_long_row_square_sum paths simple free (by omega)
  have moment : M^2 ≤ S.card*Q := by
    simpa [M,Q,S,listMassAboveWidth] using
      (sum_mul_sq_le_sq_mul_sq (R := ℕ) S (fun _ => 1) (fun i => (paths i).length))
  have m0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have realBound : (M:ℝ)^2 ≤ (ε*(n:ℝ)^2)^2 := calc
    _ ≤ (S.card:ℝ)*(Q:ℝ) := by exact_mod_cast moment
    _ ≤ ((ε^2/3)*(n:ℝ)^2)*(3*(n:ℝ)^2) :=
      mul_le_mul number (by exact_mod_cast squares) (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring
  exact (sq_le_sq₀ m0 (by positivity)).mp realBound

/-- At every full cutoff of at least three, the total mass is at most
`2p + o(n^2)` with an error uniform in the row budget. -/
theorem full_three_mass_le_twice_paths_add_subquadratic (ε : ℝ) (positive : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      ((∑ i, (paths i).length : ℕ) : ℝ) ≤ 2*(p:ℝ)+ε*(n:ℝ)^2 := by
  obtain ⟨N,small⟩ := full_three_long_mass_subquadratic ε positive
  refine ⟨N,?_⟩
  intro n p k large three paths simple free
  let S := longRows paths
  have short : (∑ i ∈ Sᶜ, (paths i).length) ≤ 2*p := calc
    _ ≤ ∑ _i ∈ Sᶜ, 2 := sum_le_sum fun i outside => by
      have large : ¬ 2 < (paths i).length := fun long => (mem_compl.mp outside) (mem_filter.mpr ⟨mem_univ _,long⟩)
      omega
    _ = 2*(Sᶜ : Finset (Fin p)).card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (by simpa only [card_univ,Fintype.card_fin] using card_le_univ (Sᶜ : Finset (Fin p)))
  have addition : (∑ i, (paths i).length) ≤ 2*p+listMassAboveWidth paths 2 := by
    rw [← sum_add_sum_compl S (fun i => (paths i).length)]
    change (∑ i ∈ S, (paths i).length)+(∑ i ∈ Sᶜ, (paths i).length) ≤ 2*p+(∑ i ∈ S, (paths i).length)
    omega
  exact (show ((∑ i, (paths i).length : ℕ):ℝ) ≤ 2*(p:ℝ)+(listMassAboveWidth paths 2:ℝ) by exact_mod_cast addition).trans
    (add_le_add_right (small large three paths simple free) _)

/-- Under full-two exclusion, all rows of length at least three have
total mass at most the square of the vertex budget. -/
theorem long_mass_le_square_of_full_two {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (two : 2 ≤ k) :
    listMassAboveWidth paths 2 ≤ n^2 := by
  have squares := full_three_long_row_square_sum paths simple free two
  have lower : 3*listMassAboveWidth paths 2 ≤ ∑ i ∈ longRows paths, (paths i).length^2 := by
    unfold listMassAboveWidth
    rw [mul_sum]
    apply sum_le_sum
    intro i on
    have long : 2 < (paths i).length := (mem_filter.mp on).2
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

end OnlineReachabilityPreservers
