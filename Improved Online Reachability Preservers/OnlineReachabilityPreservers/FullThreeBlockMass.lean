import Mathlib.Algebra.Group.Fin.Basic
import OnlineReachabilityPreservers.FullThreeLongRows

/-! A second-moment form of the full-three triangle-removal bound. -/

namespace OnlineReachabilityPreservers

open Finset Sum3
open SimpleGraph.TripartiteFromTriangles
local notation "Before" => SourceAudit.BeforeIn

private abbrev rowThird {n p : ℕ} (paths : Fin p → List (Fin n)) (i : Fin p) :=
  (paths i).length/3

private def thirdVertex {n p : ℕ} (paths : Fin p → List (Fin n)) (i : Fin p) (layer : Fin 3)
    (position : Fin (rowThird paths i)) : Fin n :=
  (paths i)[layer.val*rowThird paths i+position.val]'(by
    calc
      _ < (layer.val+1)*rowThird paths i := by rw [Nat.add_mul,Nat.one_mul]; gcongr; exact position.isLt
      _ ≤ 3*rowThird paths i := Nat.mul_le_mul_right _ layer.isLt
      _ ≤ _ := Nat.mul_div_le _ _)

private theorem thirdVertex_idx {n p : ℕ} (paths : Fin p → List (Fin n)) {i : Fin p}
    (simple : (paths i).Nodup) (layer : Fin 3) (position : Fin (rowThird paths i)) :
    (paths i).idxOf (thirdVertex paths i layer position) = layer.val*rowThird paths i+position.val := by
  apply simple.idxOf_getElem

private theorem thirdVertex_step {n p : ℕ} (paths : Fin p → List (Fin n)) {i : Fin p}
    (simple : (paths i).Nodup) {left right : Fin 3} (ordered : left < right)
    (a b : Fin (rowThird paths i)) : Before paths i (thirdVertex paths i left a) (thirdVertex paths i right b) := by
  refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
  rw [thirdVertex_idx paths simple,thirdVertex_idx paths simple]
  calc
    _ < (left.val+1)*rowThird paths i := by rw [Nat.add_mul,Nat.one_mul]; gcongr; exact a.isLt
    _ ≤ right.val*rowThird paths i := Nat.mul_le_mul_right _ ordered
    _ ≤ _ := Nat.le_add_right _ _

private theorem thirdVertex_injective {n p : ℕ} (paths : Fin p → List (Fin n)) {i : Fin p}
    (simple : (paths i).Nodup) (layer : Fin 3) : Function.Injective (thirdVertex paths i layer) := by
  intro a b equal
  have indices := congrArg (paths i).idxOf equal
  rw [thirdVertex_idx paths simple,thirdVertex_idx paths simple] at indices
  exact Fin.ext (Nat.add_left_cancel indices)

private theorem thirdVertex_owner {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 2)
    {i j : Fin p} {left right : Fin 3} (ordered : left < right) {a b : Fin (rowThird paths i)}
    {c d : Fin (rowThird paths j)} (first : thirdVertex paths i left a = thirdVertex paths j left c)
    (second : thirdVertex paths i right b = thirdVertex paths j right d) : i = j := by
  by_contra different
  have beforeI := thirdVertex_step paths (simple i) ordered a b
  have beforeJ := thirdVertex_step paths (simple j) ordered c d
  rw [← first,← second] at beforeJ
  exact no_parallel_list_steps free le_rfl different beforeI beforeJ

private abbrev ThirdTriples {n p : ℕ} (paths : Fin p → List (Fin n)) :=
  Σ i : Fin p, Fin (rowThird paths i) × Fin (rowThird paths i) × Fin (rowThird paths i)

private def thirdTriple {n p : ℕ} (paths : Fin p → List (Fin n)) (i : ThirdTriples paths) : Fin n × Fin n × Fin n :=
  (thirdVertex paths i.1 0 i.2.1,thirdVertex paths i.1 1 i.2.2.1,thirdVertex paths i.1 2 i.2.2.2)

private theorem thirdTriple_injective {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 2) :
    Function.Injective (thirdTriple paths) := by
  rintro ⟨i,a,b,c⟩ ⟨j,x,y,z⟩ equal
  obtain ⟨aEq,bEq,cEq⟩ : thirdVertex paths i 0 a = thirdVertex paths j 0 x ∧
      thirdVertex paths i 1 b = thirdVertex paths j 1 y ∧ thirdVertex paths i 2 c = thirdVertex paths j 2 z :=
    ⟨congrArg Prod.fst equal,congrArg (fun r => r.2.1) equal,congrArg (fun r => r.2.2) equal⟩
  obtain rfl := thirdVertex_owner paths simple free (by decide : (0:Fin 3) < 1) aEq bEq
  obtain rfl := thirdVertex_injective paths (simple i) 0 aEq
  obtain rfl := thirdVertex_injective paths (simple i) 1 bEq
  obtain rfl := thirdVertex_injective paths (simple i) 2 cEq
  rfl

private def thirdTriangles {n p : ℕ} (paths : Fin p → List (Fin n)) : Finset (Fin n × Fin n × Fin n) :=
  (univ : Finset (ThirdTriples paths)).image (thirdTriple paths)

private theorem thirdTriangles_card {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 2) :
    (thirdTriangles paths).card = ∑ i, (rowThird paths i)^3 := by
  rw [thirdTriangles,card_image_of_injective _ (thirdTriple_injective paths simple free),card_univ]
  simp [Fintype.card_sigma,pow_succ,Nat.mul_assoc]

private theorem thirdTriangle_witness {n p : ℕ} {paths : Fin p → List (Fin n)} {a b c : Fin n}
    (on : (a,b,c) ∈ thirdTriangles paths) :
    ∃ (i : Fin p) (u v w : Fin (rowThird paths i)),
      thirdVertex paths i 0 u = a ∧ thirdVertex paths i 1 v = b ∧ thirdVertex paths i 2 w = c := by
  obtain ⟨⟨i,u,v,w⟩,_,equal⟩ := mem_image.mp on
  exact ⟨i,u,v,w,congrArg Prod.fst equal,congrArg (fun r => r.2.1) equal,congrArg (fun r => r.2.2) equal⟩

private theorem thirdTriangles_card_cliques {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) (three : 3 ≤ k) :
    ((graph (thirdTriangles paths)).cliqueFinset 3).card = ∑ i, (rowThird paths i)^3 := by
  let t := thirdTriangles paths
  have two : HalfBridgeFree (Before paths) 2 := fun _ size => free.halfFree (size.trans (by omega))
  have triangles : (graph t).cliqueFinset 3 = t.map toTriangle := by
    ext s
    rw [SimpleGraph.mem_cliqueFinset_iff]
    constructor
    · intro h
      rw [SimpleGraph.is3Clique_iff] at h
      obtain ⟨x,y,z,xy,xz,yz,rfl⟩ := h
      obtain ⟨a,b,c,same,ab,ac,bc⟩ := graph_triple xy xz yz
      rw [← same]
      obtain ⟨c',ab⟩ := Graph.in₀₁_iff.mp ab
      obtain ⟨b',ac⟩ := Graph.in₀₂_iff.mp ac
      obtain ⟨a',bc⟩ := Graph.in₁₂_iff.mp bc
      obtain ⟨i,u,v,w,au,bv,_⟩ := thirdTriangle_witness ab
      obtain ⟨j,u',v',w',_,bv',cw'⟩ := thirdTriangle_witness bc
      obtain ⟨r,u'',v'',w'',au'',_,cw''⟩ := thirdTriangle_witness ac
      have on : (a,b,c) ∈ t := by
        by_cases equal : i = j
        · subst j
          exact mem_image.mpr ⟨⟨i,u,v,w'⟩,mem_univ _,Prod.ext au (Prod.ext bv cw')⟩
        by_cases equalRiver : r = i
        · subst r
          exact mem_image.mpr ⟨⟨i,u,v,w''⟩,mem_univ _,Prod.ext au (Prod.ext bv cw'')⟩
        by_cases equalLast : r = j
        · subst r
          exact mem_image.mpr ⟨⟨j,u'',v',w'⟩,mem_univ _,Prod.ext au'' (Prod.ext bv' cw')⟩
        have first : Before paths i a b := au ▸ bv ▸ thirdVertex_step paths (simple i) (by decide : (0:Fin 3) < 1) u v
        have last : Before paths j b c := bv' ▸ cw' ▸ thirdVertex_step paths (simple j) (by decide : (1:Fin 3) < 2) v' w'
        have river : Before paths r a c := au'' ▸ cw'' ▸ thirdVertex_step paths (simple r) (by decide : (0:Fin 3) < 2) u'' w''
        exact ((free three).false (threeListBridge equal equalRiver equalLast first last river)).elim
      exact mem_map.mpr ⟨(a,b,c),on,rfl⟩
    · rintro h
      obtain ⟨t',hit,rfl⟩ := mem_map.mp h
      exact toTriangle_is3Clique hit
  change ((graph t).cliqueFinset 3).card = _
  rw [triangles,card_map,thirdTriangles_card paths simple two]

private abbrev ThirdPairs {n p : ℕ} (paths : Fin p → List (Fin n)) :=
  Σ i : Fin p, Fin (rowThird paths i) × Fin (rowThird paths i)

private def latinTriple {n p : ℕ} (paths : Fin p → List (Fin n)) (i : ThirdPairs paths) : ThirdTriples paths :=
  ⟨i.1,i.2.1,i.2.2,i.2.1+i.2.2⟩

private theorem latinTriple_injective {n p : ℕ} (paths : Fin p → List (Fin n)) :
    Function.Injective (latinTriple paths) := by
  rintro ⟨i,a,b⟩ ⟨j,x,y⟩ equal
  have first : i = j := congrArg Sigma.fst equal
  subst j
  have triple : (a,b,a+b) = (x,y,x+y) := eq_of_heq (Sigma.mk.inj_iff.mp equal).2
  obtain ⟨ax,pair⟩ := Prod.mk.inj triple
  obtain ⟨rfl,_⟩ := Prod.mk.inj pair
  subst x
  rfl

private theorem first_two_third_vertices_injective {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 2) :
    Function.Injective (fun i : ThirdPairs paths =>
      (thirdVertex paths i.1 0 i.2.1,thirdVertex paths i.1 1 i.2.2)) := by
  rintro ⟨i,a,b⟩ ⟨j,x,y⟩ equal
  obtain ⟨hx,hy⟩ := Prod.mk.inj equal
  obtain rfl := thirdVertex_owner paths simple free (by decide : (0:Fin 3) < 1) hx hy
  obtain rfl := thirdVertex_injective paths (simple i) 0 hx
  obtain rfl := thirdVertex_injective paths (simple i) 1 hy
  rfl

private theorem thirdSquare_le_vertexSquare {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 2) :
    (∑ i, (rowThird paths i)^2) ≤ n^2 := by
  simpa [Fintype.card_sigma,pow_two] using Fintype.card_le_of_injective _
    (first_two_third_vertices_injective paths simple free)

private def latinTriangles {n p : ℕ} (paths : Fin p → List (Fin n)) : Finset (Fin n × Fin n × Fin n) :=
  (univ : Finset (ThirdPairs paths)).image (thirdTriple paths ∘ latinTriple paths)

private theorem latinTriangles_subset {n p : ℕ} (paths : Fin p → List (Fin n)) :
    latinTriangles paths ⊆ thirdTriangles paths := by
  intro x hit
  obtain ⟨i,_,equal⟩ := mem_image.mp hit
  exact mem_image.mpr ⟨latinTriple paths i,mem_univ _,equal⟩

private theorem latinTriangles_card {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 2) :
    (latinTriangles paths).card = ∑ i, (rowThird paths i)^2 := by
  rw [latinTriangles,card_image_of_injective _ ((thirdTriple_injective paths simple free).comp
    (latinTriple_injective paths)),card_univ]
  simp [Fintype.card_sigma,pow_two]

private theorem latinTriangles_disjoint {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 2) :
    ExplicitDisjoint (latinTriangles paths) := by
  have witness {a b c : Fin n} (on : (a,b,c) ∈ latinTriangles paths) :
      ∃ (i : Fin p) (u v : Fin (rowThird paths i)),
        thirdVertex paths i 0 u = a ∧ thirdVertex paths i 1 v = b ∧ thirdVertex paths i 2 (u+v) = c := by
    obtain ⟨⟨i,u,v⟩,_,same⟩ := mem_image.mp on
    exact ⟨i,u,v,congrArg Prod.fst same,congrArg (fun x => x.2.1) same,congrArg (fun x => x.2.2) same⟩
  constructor
  · intro a b c a' hit next
    obtain ⟨i,u,v,au,bv,csum⟩ := witness hit
    obtain ⟨j,u',v',au',bv',csum'⟩ := witness next
    obtain rfl := thirdVertex_owner paths simple free (by decide : (1:Fin 3) < 2) (bv.trans bv'.symm) (csum.trans csum'.symm)
    obtain rfl := thirdVertex_injective paths (simple i) 1 (bv.trans bv'.symm)
    have same := thirdVertex_injective paths (simple i) 2 (csum.trans csum'.symm)
    obtain rfl := add_right_cancel same
    exact au.symm.trans au'
  · intro a b c b' hit next
    obtain ⟨i,u,v,au,bv,csum⟩ := witness hit
    obtain ⟨j,u',v',au',bv',csum'⟩ := witness next
    obtain rfl := thirdVertex_owner paths simple free (by decide : (0:Fin 3) < 2) (au.trans au'.symm) (csum.trans csum'.symm)
    obtain rfl := thirdVertex_injective paths (simple i) 0 (au.trans au'.symm)
    have same := thirdVertex_injective paths (simple i) 2 (csum.trans csum'.symm)
    obtain rfl := add_left_cancel same
    exact bv.symm.trans bv'
  · intro a b c c' hit next
    obtain ⟨i,u,v,au,bv,csum⟩ := witness hit
    obtain ⟨j,u',v',au',bv',csum'⟩ := witness next
    obtain rfl := thirdVertex_owner paths simple free (by decide : (0:Fin 3) < 1) (au.trans au'.symm) (bv.trans bv'.symm)
    obtain rfl := thirdVertex_injective paths (simple i) 0 (au.trans au'.symm)
    obtain rfl := thirdVertex_injective paths (simple i) 1 (bv.trans bv'.symm)
    exact csum.symm.trans csum'

/-- At each fixed density tolerance, rows whose lengths are all at most
a sufficiently small fixed fraction of the vertex budget have a small
sum of squared third widths. The tolerance is independent of the row budget. -/
theorem full_three_third_square_sum_of_short_rows (ε : ℝ) (positive : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {n p k : ℕ}, 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      (∀ i, ((paths i).length:ℝ) ≤ ρ*n) →
      ((∑ i, ((paths i).length/3)^2 : ℕ):ℝ) ≤ ε*(n:ℝ)^2 := by
  let δ := SimpleGraph.triangleRemovalBound (ε/9)
  have δPos : 0 < δ := SimpleGraph.triangleRemovalBound_pos (by positivity)
  refine ⟨δ,δPos,?_⟩
  intro n p k three paths simple free short
  let all := thirdTriangles paths
  let packed := latinTriangles paths
  have two : HalfBridgeFree (Before paths) 2 := fun _ size => free.halfFree (size.trans (by omega))
  let : ExplicitDisjoint packed := latinTriangles_disjoint paths simple two
  by_contra! dense
  change ε*(n:ℝ)^2 < ((∑ i, (rowThird paths i)^2 : ℕ):ℝ) at dense
  have far : (graph all).FarFromTriangleFree (ε/9) := by
    apply SimpleGraph.farFromTriangleFree_of_disjoint_triangles (packed.map toTriangle)
    · intro s hit
      obtain ⟨t,ht,rfl⟩ := mem_map.mp hit
      exact SimpleGraph.mem_cliqueFinset_iff.mpr (toTriangle_is3Clique (latinTriangles_subset paths ht))
    · exact map_toTriangle_disjoint packed
    · rw [card_map]
      change (ε/9)*((Fintype.card (Fin n ⊕ Fin n ⊕ Fin n))^2:ℕ) ≤ (latinTriangles paths).card
      rw [latinTriangles_card paths simple two]
      simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_pow,Nat.cast_add]
      convert dense.le using 1
      ring
  have lower := far.le_card_cliqueFinset
  change δ*(Fintype.card (Fin n ⊕ Fin n ⊕ Fin n):ℝ)^3 ≤ ((graph (thirdTriangles paths)).cliqueFinset 3).card at lower
  rw [thirdTriangles_card_cliques paths simple free three] at lower
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add] at lower
  have cap : ((∑ i, (rowThird paths i)^2 : ℕ):ℝ) ≤ (n:ℝ)^2 := by
    exact_mod_cast thirdSquare_le_vertexSquare paths simple two
  have upper : ((∑ i, (rowThird paths i)^3 : ℕ):ℝ) ≤ δ*(n:ℝ)^3 := by
    calc
      _ = ∑ i, ((rowThird paths i:ℝ)^2)*(rowThird paths i:ℝ) := by push_cast; simp [pow_succ]
      _ ≤ ∑ i, ((rowThird paths i:ℝ)^2)*(δ*(n:ℝ)) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          ((Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (short i)) (by positivity)
      _ = ((∑ i, (rowThird paths i)^2 : ℕ):ℝ)*(δ*(n:ℝ)) := by
        simp only [Nat.cast_sum,Nat.cast_pow,sum_mul]
      _ ≤ (n:ℝ)^2*(δ*(n:ℝ)) := mul_le_mul_of_nonneg_right cap (by positivity)
      _ = _ := by ring
  have nPos : (0:ℝ) < n := by
    by_contra! small
    have zero : (n:ℝ) = 0 := le_antisymm small (Nat.cast_nonneg n)
    norm_num [zero] at dense cap
    exact (not_lt_of_ge cap) dense
  have strict : δ*(n:ℝ)^3 < δ*((n:ℝ)+((n:ℝ)+(n:ℝ)))^3 := by gcongr; linarith
  exact (not_lt_of_ge upper) (strict.trans_le lower)

private theorem rowLength_square_le_third_square {L : ℕ} (long : 2 < L) : L^2 ≤ 25*(L/3)^2 := by
  have length : L ≤ 5*(L/3) := by omega
  calc
    _ ≤ (5*(L/3))^2 := Nat.pow_le_pow_left length 2
    _ = _ := by ring

/-- For every positive `ε`, the mass of long rows is at most
`ε n √p + C n` at all full cutoffs from three, with `C` depending only on `ε`.
Rows of length more than a fixed fraction of `n` cost the linear term. -/
theorem full_three_long_mass_le_small_n_sqrt_p_add_linear (ε : ℝ) (positive : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n p k : ℕ}, 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      (listMassAboveWidth paths 2:ℝ) ≤ ε*(n:ℝ)*Real.sqrt p+C*n := by
  obtain ⟨ρ,ρPos,small⟩ := full_three_third_square_sum_of_short_rows (ε^2/25) (by positivity)
  refine ⟨25/ρ,by positivity,?_⟩
  intro n p k three paths simple free
  have two : HalfBridgeFree (Before paths) 2 := fun _ size => free.halfFree (size.trans (by omega))
  let S := univ.filter (fun i : Fin p => 2 < (paths i).length ∧ ((paths i).length:ℝ) ≤ ρ*n)
  let T := univ.filter (fun i : Fin p => 2 < (paths i).length ∧ ρ*n < ((paths i).length:ℝ))
  let masked (i : Fin p) := if i ∈ S then paths i else []
  have maskSub (i : Fin p) : (masked i).Sublist (paths i) := by by_cases on : i ∈ S <;> simp [masked,on]
  have maskFree : BridgeFree (Before masked) k := fun _ limit =>
    ⟨fun b => (free limit).false (b.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (maskSub i) step))⟩
  have maskShort (i : Fin p) : ((masked i).length:ℝ) ≤ ρ*n := by
    by_cases on : i ∈ S
    · simpa only [masked,ite_eq_left on] using (mem_filter.mp on).2.2
    · simpa only [masked,ite_eq_right on,List.length_nil,Nat.cast_zero] using
        mul_nonneg ρPos.le (Nat.cast_nonneg n)
  have maskedSquare := small three masked (fun i => (maskSub i).nodup (simple i)) maskFree maskShort
  have moment : (∑ i, (masked i).length^2) ≤ 25*(∑ i, ((masked i).length/3)^2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    by_cases on : i ∈ S
    · rw [show masked i = paths i from ite_eq_left on]
      exact rowLength_square_le_third_square (mem_filter.mp on).2.1
    · simp [masked,on]
  have smallSquare : (∑ i, ((masked i).length:ℝ)^2) ≤ (ε*(n:ℝ))^2 := calc
    _ ≤ 25*((∑ i, ((masked i).length/3)^2 : ℕ):ℝ) := by exact_mod_cast moment
    _ ≤ 25*((ε^2/25)*(n:ℝ)^2) := mul_le_mul_of_nonneg_left maskedSquare (by norm_num)
    _ = _ := by ring
  have cauchy : (∑ i, ((masked i).length:ℝ))^2 ≤ (p:ℝ)*(∑ i, ((masked i).length:ℝ)^2) := by
    simpa using (sum_mul_sq_le_sq_mul_sq (R := ℝ) (univ : Finset (Fin p)) (fun _ => 1)
      (fun i => ((masked i).length:ℝ)))
  have smallBound : (∑ i, ((masked i).length:ℝ)) ≤ ε*(n:ℝ)*Real.sqrt p := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      _ ≤ (p:ℝ)*(∑ i, ((masked i).length:ℝ)^2) := cauchy
      _ ≤ (p:ℝ)*(ε*(n:ℝ))^2 := mul_le_mul_of_nonneg_left smallSquare (by positivity)
      _ = (ε*(n:ℝ)*Real.sqrt p)^2 := by
        rw [mul_pow (ε*(n:ℝ)) (Real.sqrt p),Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  have largeCost : (ρ*(n:ℝ))*(∑ i ∈ T, ((paths i).length:ℝ)) ≤ 25*(n:ℝ)^2 := calc
    _ = ∑ i ∈ T, (ρ*(n:ℝ))*((paths i).length:ℝ) := by rw [mul_sum]
    _ ≤ ∑ i ∈ T, ((paths i).length:ℝ)^2 := sum_le_sum fun i hit => by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (mem_filter.mp hit).2.2.le (by positivity)
    _ ≤ ∑ i ∈ T, 25*(rowThird paths i:ℝ)^2 := sum_le_sum fun i hit => by
      exact_mod_cast rowLength_square_le_third_square (mem_filter.mp hit).2.1
    _ ≤ ∑ i, 25*(rowThird paths i:ℝ)^2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
    _ = 25*((∑ i, (rowThird paths i)^2 : ℕ):ℝ) := by
      simp only [Nat.cast_sum,Nat.cast_pow,mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast thirdSquare_le_vertexSquare paths simple two) (by norm_num)
  by_cases hn : 0 < n
  swap
  · have mass := long_mass_le_square_of_full_two paths simple free (by omega)
    have zero : (n:ℝ) = 0 := by exact_mod_cast (show n = 0 by omega)
    have cap : (listMassAboveWidth paths 2:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast mass
    simpa [zero] using cap
  have largeBound : (∑ i ∈ T, ((paths i).length:ℝ)) ≤ (25/ρ)*(n:ℝ) := by
    apply (le_of_mul_le_mul_left · (show 0 < ρ*(n:ℝ) by positivity))
    convert largeCost using 1
    field_simp [ρPos.ne']
  have split : (listMassAboveWidth paths 2:ℝ) =
      (∑ i, ((masked i).length:ℝ)) + ∑ i ∈ T, ((paths i).length:ℝ) := by
    unfold listMassAboveWidth
    push_cast
    rw [sum_filter,show T = univ.filter (fun i : Fin p => 2 < (paths i).length ∧ ρ*n < ((paths i).length:ℝ)) from rfl,
      sum_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    by_cases long : 2 < (paths i).length
    · rcases le_or_gt ((paths i).length:ℝ) (ρ*n) with short | tall
      · simp [S,masked,long,short,not_lt_of_ge short]
      · simp [S,masked,long,tall,not_le_of_gt tall]
    · simp [S,masked,long]
  rw [split]
  exact add_le_add smallBound largeBound

/-- The full-three long mass is `o(n √p)` uniformly in the vertex
budget and all smaller pairs of budgets as the path budget tends to infinity. -/
theorem full_three_long_mass_small_n_sqrt_p_within_budgets (a : ℝ) (positive : 0 < a) :
    ∃ P : ℕ, 0 < P ∧ ∀ {n p v q k : ℕ}, P ≤ p → v ≤ n → q ≤ p → 3 ≤ k →
      ∀ paths : Fin q → List (Fin v), (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k →
      (listMassAboveWidth paths 2:ℝ) ≤ a*(n:ℝ)*Real.sqrt p := by
  let ε := a/2
  have εPos : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C,CPos,uniform⟩ := full_three_long_mass_le_small_n_sqrt_p_add_linear ε εPos
  refine ⟨⌈(C/ε)^2⌉₊+1,by positivity,?_⟩
  intro n p v q k large vertices rows three paths simple free
  have divide : (C/ε)^2 ≤ (p:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
  have paid : C ≤ ε*Real.sqrt p := by
    have length : C/ε ≤ Real.sqrt p := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      exact divide
    simpa only [mul_comm] using (div_le_iff₀ εPos).mp length
  have qFits : Real.sqrt q ≤ Real.sqrt p := Real.sqrt_le_sqrt (Nat.cast_le.mpr rows)
  have vFits : (v:ℝ) ≤ n := Nat.cast_le.mpr vertices
  calc
    _ ≤ ε*(v:ℝ)*Real.sqrt q+C*v := uniform three paths simple free
    _ ≤ ε*(n:ℝ)*Real.sqrt p+C*n := by gcongr
    _ ≤ ε*(n:ℝ)*Real.sqrt p+(ε*Real.sqrt p)*(n:ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right paid (Nat.cast_nonneg n))
    _ = _ := by dsimp only [ε]; ring

/-- The original lower cap obstructs full exclusion at a mass of order
`n √p` and original mean length greater than eight, when the output must
fit both budgets and the original path budget is sufficiently large. -/
theorem full_frozen_high_mean_excludes_n_sqrt_p_retention (η : ℝ) (positive : 0 < η)
    (retention : ℕ) (retentionPositive : 0 < retention) :
    ∃ P : ℕ, ∀ {n p M v q k : ℕ}, P ≤ p → v ≤ n → q ≤ p → 3 ≤ k → 8*p < M →
      η*(n:ℝ)*Real.sqrt p ≤ M → ∀ paths : Fin q → List (Fin v),
      (∀ i, (paths i).Nodup) → BridgeFree (Before paths) k → frozenListCaps n p M paths →
      retention*(∑ i, (paths i).length) < M := by
  let ε := η/(2*(retention:ℝ))
  have εPos : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨P,PPos,small⟩ := full_three_long_mass_small_n_sqrt_p_within_budgets ε εPos
  refine ⟨P,?_⟩
  intro n p M v q k large vertices rows three high dense paths simple free caps
  have pPos : 0 < p := PPos.trans_le large
  have mean : (2:ℝ) < (M:ℝ)/(4*(p:ℝ)) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    have h : (8:ℝ)*p < M := by exact_mod_cast high
    linarith only [h]
  have long (i : Fin q) : 2 < (paths i).length := by exact_mod_cast mean.trans_le (caps.2 i).1
  have mass : listMassAboveWidth paths 2 = ∑ i, (paths i).length := by
    unfold listMassAboveWidth
    simp [long]
  have fit : ((∑ i, (paths i).length : ℕ):ℝ) ≤ ε*(n:ℝ)*Real.sqrt p := by
    rw [← mass]
    exact small large vertices rows three paths simple free
  have rPos : (0:ℝ) < retention := Nat.cast_pos.mpr retentionPositive
  have factor : (retention:ℝ)*ε = η/2 := by dsimp [ε]; field_simp [rPos.ne']
  have retained : (retention:ℝ)*((∑ i, (paths i).length : ℕ):ℝ) ≤ (M:ℝ)/2 := calc
    _ ≤ (retention:ℝ)*(ε*(n:ℝ)*Real.sqrt p) := mul_le_mul_of_nonneg_left fit rPos.le
    _ = (η*(n:ℝ)*Real.sqrt p)/2 := by rw [← mul_assoc,← mul_assoc,factor]; ring
    _ ≤ _ := div_le_div_of_nonneg_right dense (by norm_num)
  have mPos : (0:ℝ) < M := Nat.cast_pos.mpr (by omega)
  exact_mod_cast retained.trans_lt (by linarith only [mPos] : (M:ℝ)/2 < M)

end OnlineReachabilityPreservers
