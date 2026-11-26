import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! Frozen cleaning by sparse witnesses, paired paths, and bipartite blocks. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private def frozenRectangleVertex {r w : ℕ} (block : Fin r) (side : Fin 2) (offset : Fin w) :
    Fin (r*(2*w)) :=
  finProdFinEquiv (block,finProdFinEquiv (side,offset))

private def frozenRectangleCoords {r w : ℕ} (i : Fin (r*(w*w))) : Fin r × (Fin w × Fin w) :=
  let pair : Fin r × Fin (w*w) := finProdFinEquiv.symm i
  (pair.1,finProdFinEquiv.symm pair.2)

private def frozenRectangleIndex {r w : ℕ} (block : Fin r) (left right : Fin w) : Fin (r*(w*w)) :=
  finProdFinEquiv (block,finProdFinEquiv (left,right))

private theorem frozenRectangleCoords_index {r w : ℕ} (block : Fin r) (left right : Fin w) :
    frozenRectangleCoords (frozenRectangleIndex block left right) = (block,left,right) := by
  simp only [frozenRectangleCoords,frozenRectangleIndex,Equiv.symm_apply_apply]

private theorem frozenRectangleCoords_injective {r w : ℕ} :
    Function.Injective (@frozenRectangleCoords r w) := by
  intro x y same
  apply (finProdFinEquiv : Fin r × Fin (w*w) ≃ Fin (r*(w*w))).symm.injective
  have blocks := congrArg (fun z : Fin r × (Fin w × Fin w) => z.1) same
  have offsets := congrArg (fun z : Fin r × (Fin w × Fin w) => z.2) same
  exact Prod.ext blocks ((finProdFinEquiv : Fin w × Fin w ≃ Fin (w*w)).symm.injective offsets)

private theorem frozenRectangleVertex_eq {r w : ℕ} {a b : Fin r} {s t : Fin 2} {i j : Fin w}
    (eq : frozenRectangleVertex a s i = frozenRectangleVertex b t j) :
    a = b ∧ s = t ∧ i = j := by
  have outer := (finProdFinEquiv : Fin r × Fin (2*w) ≃ Fin (r*(2*w))).injective eq
  have inner := (finProdFinEquiv : Fin 2 × Fin w ≃ Fin (2*w)).injective (congrArg Prod.snd outer)
  exact ⟨congrArg Prod.fst outer, congrArg Prod.fst inner, congrArg Prod.snd inner⟩

private def frozenRectangleRows (r w : ℕ) (i : Fin (r*(w*w))) : List (Fin (r*(2*w))) :=
  let coords := frozenRectangleCoords i
  [frozenRectangleVertex coords.1 0 coords.2.1, frozenRectangleVertex coords.1 1 coords.2.2]

private theorem frozenRectangleRows_simple {r w : ℕ} (i : Fin (r*(w*w))) :
    (frozenRectangleRows r w i).Nodup := by
  simp only [frozenRectangleRows,List.nodup_cons,List.nodup_nil,List.mem_cons,List.not_mem_nil,
    or_false,not_false_eq_true,and_true]
  intro eq
  exact (by decide : (0 : Fin 2) ≠ 1) (frozenRectangleVertex_eq eq).2.1

private theorem frozenRectangleRows_step {r w : ℕ} {i : Fin (r*(w*w))} {x y : Fin (r*(2*w))}
    (step : ListBefore (frozenRectangleRows r w) i x y) :
    x = frozenRectangleVertex (frozenRectangleCoords i).1 0 (frozenRectangleCoords i).2.1 ∧
    y = frozenRectangleVertex (frozenRectangleCoords i).1 1 (frozenRectangleCoords i).2.2 := by
  let coords := frozenRectangleCoords i
  let left := frozenRectangleVertex coords.1 0 coords.2.1
  let right := frozenRectangleVertex coords.1 1 coords.2.2
  have apart : left ≠ right := fun same => (by decide : (0 : Fin 2) ≠ 1) (frozenRectangleVertex_eq same).2.1
  have hx : x = left ∨ x = right := by
    simpa only [frozenRectangleRows,List.mem_cons,List.not_mem_nil,or_false] using step.1
  have hy : y = left ∨ y = right := by
    simpa only [frozenRectangleRows,List.mem_cons,List.not_mem_nil,or_false] using step.2.1
  have order : [left,right].idxOf x < [left,right].idxOf y := step.2.2
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (Nat.lt_irrefl _ order).elim
  · exact ⟨rfl,rfl⟩
  · simp [apart] at order
  · exact (Nat.lt_irrefl _ order).elim

private theorem frozenRectangleRows_free (r w k : ℕ) : BridgeFree (ListBefore (frozenRectangleRows r w)) k := by
  intro q _
  refine ⟨fun b => ?_⟩
  cases q with
  | zero =>
    have river := frozenRectangleRows_step b.riverStep
    have arc := frozenRectangleRows_step (b.arcStep 0)
    have start : frozenRectangleVertex (frozenRectangleCoords b.river).1 0 (frozenRectangleCoords b.river).2.1 =
        frozenRectangleVertex (frozenRectangleCoords (b.arc 0)).1 0 (frozenRectangleCoords (b.arc 0)).2.1 :=
      river.1.symm.trans arc.1
    have last : frozenRectangleVertex (frozenRectangleCoords b.river).1 1 (frozenRectangleCoords b.river).2.2 =
        frozenRectangleVertex (frozenRectangleCoords (b.arc 0)).1 1 (frozenRectangleCoords (b.arc 0)).2.2 :=
      river.2.symm.trans arc.2
    have root := frozenRectangleVertex_eq start
    have target := frozenRectangleVertex_eq last
    exact b.river_ne_arc 0 (frozenRectangleCoords_injective (Prod.ext root.1 (Prod.ext root.2.2 target.2.2)))
  | succ q =>
    have left := (frozenRectangleRows_step (b.arcStep 0)).2
    have right := (frozenRectangleRows_step (b.arcStep 1)).1
    exact (by decide : (1 : Fin 2) ≠ 0) (frozenRectangleVertex_eq (left.symm.trans right)).2.1

private theorem frozenRectangleRows_degree (r w : ℕ) (x : Fin (r*(2*w))) :
    (occurrences (fun i => (frozenRectangleRows r w i).toFinset) x).card = w := by
  let pair : Fin r × Fin (2*w) := finProdFinEquiv.symm x
  let q : Fin 2 × Fin w := finProdFinEquiv.symm pair.2
  have location : x = frozenRectangleVertex pair.1 q.1 q.2 := by
    unfold frozenRectangleVertex
    rw [Prod.mk.eta,Equiv.apply_symm_apply,Prod.mk.eta,Equiv.apply_symm_apply]
  let family (t : Fin w) := if q.1 = 0 then frozenRectangleIndex pair.1 q.2 t
    else frozenRectangleIndex pair.1 t q.2
  have injective : Function.Injective family := by
    intro a b same
    by_cases side : q.1 = 0
    · simp only [family,side,ite_true] at same
      have index := congrArg frozenRectangleCoords same
      simp only [frozenRectangleCoords_index, Prod.mk.injEq, true_and] at index
      exact index
    · simp only [family,side,ite_false] at same
      have index := congrArg frozenRectangleCoords same
      simp only [frozenRectangleCoords_index,Prod.mk.injEq,true_and,and_true] at index
      exact index
  let index : Fin w ↪ Fin (r*(w*w)) := ⟨family,injective⟩
  have eq : occurrences (fun i => (frozenRectangleRows r w i).toFinset) x = univ.map index := by
    ext i
    simp only [mem_occurrences,List.mem_toFinset,mem_map,mem_univ,true_and]
    have iEq : frozenRectangleIndex (frozenRectangleCoords i).1 (frozenRectangleCoords i).2.1
        (frozenRectangleCoords i).2.2 = i := by
      apply frozenRectangleCoords_injective
      simp only [frozenRectangleCoords_index,Prod.mk.eta]
    by_cases side : q.1 = 0
    · constructor
      · intro member
        rw [location, side] at member
        rcases (show _ ∨ _ from by simpa only [frozenRectangleRows,List.mem_cons,List.not_mem_nil,or_false] using member) with first | second
        · have same := frozenRectangleVertex_eq first
          refine ⟨(frozenRectangleCoords i).2.2,?_⟩
          change family (frozenRectangleCoords i).2.2 = i
          simp only [family,side,ite_true]
          rw [same.1, same.2.2]
          exact iEq
        · exact ((by decide : (0 : Fin 2) ≠ 1) (frozenRectangleVertex_eq second).2.1).elim
      · rintro ⟨t,rfl⟩
        change x ∈ frozenRectangleRows r w (family t)
        simp only [family,side,ite_true,frozenRectangleRows,frozenRectangleCoords_index,
          List.mem_cons,List.not_mem_nil,or_false]
        exact Or.inl (by simpa only [side] using location)
    · have one : q.1 = 1 := Fin.ext (by
        have bound := q.1.isLt
        have notZero : q.1.val ≠ 0 := fun same => side (Fin.ext same)
        omega)
      constructor
      · intro member
        rw [location, one] at member
        rcases (show _ ∨ _ from by simpa only [frozenRectangleRows,List.mem_cons,List.not_mem_nil,or_false] using member) with first | second
        · exact ((by decide : (1 : Fin 2) ≠ 0) (frozenRectangleVertex_eq first).2.1).elim
        · have same := frozenRectangleVertex_eq second
          refine ⟨(frozenRectangleCoords i).2.1,?_⟩
          change family (frozenRectangleCoords i).2.1 = i
          simp only [family,side,ite_false]
          rw [same.1, same.2.2]
          exact iEq
      · rintro ⟨t,rfl⟩
        change x ∈ frozenRectangleRows r w (family t)
        simp only [family,side,ite_false,frozenRectangleRows,frozenRectangleCoords_index,
          List.mem_cons,List.not_mem_nil,or_false]
        exact Or.inr (by simpa only [one] using location)
  rw [eq,card_map,card_univ,Fintype.card_fin]

/-- Consecutive edges are distinct across simple paths when 2-bridges are
excluded, so their total count is at most the number of off-diagonal pairs. -/
theorem listMass_le_ordered_pairs_add_paths {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k) :
    (∑ i, (paths i).length) ≤ n*(n-1)+p := by
  let index := Σ i : Fin p, Fin ((paths i).length-1)
  let first (i : index) : Fin n := (paths i.1)[i.2.val]'(by have fit := i.2.isLt; omega)
  let next (i : index) : Fin n := (paths i.1)[i.2.val+1]'(by have fit := i.2.isLt; omega)
  have step (i : index) : ListBefore paths i.1 (first i) (next i) := by
    refine ⟨List.getElem_mem _,List.getElem_mem _,?_⟩
    dsimp only [first,next]
    rw [(simple i.1).idxOf_getElem,(simple i.1).idxOf_getElem]
    omega
  let target : Finset (Fin n × Fin n) := (univ : Finset (Fin n)).offDiag
  let edge (i : index) : target :=
    ⟨(first i,next i),Finset.mem_offDiag.mpr ⟨mem_univ _,mem_univ _,listBefore_ne (step i)⟩⟩
  have injective : Function.Injective edge := by
    intro a b same
    have left := congrArg (fun e : target => e.val.1) same
    have right := congrArg (fun e : target => e.val.2) same
    change first a = first b at left
    change next a = next b at right
    by_cases matchPath : a.1 = b.1
    · obtain ⟨i,u⟩ := a
      obtain ⟨j,v⟩ := b
      dsimp only at matchPath
      subst j
      have equal := congrArg ((paths i).idxOf) left
      dsimp only [first] at equal
      rw [(simple i).idxOf_getElem,(simple i).idxOf_getElem] at equal
      cases Fin.ext equal
      rfl
    · have parallel := step b
      rw [← left,← right] at parallel
      exact (no_parallel_list_steps free cutoff matchPath (step a) parallel).elim
  have count := Fintype.card_le_of_injective edge injective
  change Fintype.card (Σ i : Fin p, Fin ((paths i).length-1)) ≤ Fintype.card target at count
  have edges : (∑ i, ((paths i).length-1)) ≤ n*(n-1) := by
    rw [Fintype.card_sigma,Fintype.card_coe,show target.card = n*(n-1) by
      simp only [target,Finset.offDiag_card,card_univ,Fintype.card_fin,Nat.mul_sub_left_distrib,Nat.mul_one]]
      at count
    simpa only [Fintype.card_fin] using count
  calc
    _ ≤ ∑ i : Fin p, (((paths i).length-1)+1) := sum_le_sum (fun i _ => by omega)
    _ = (∑ i, ((paths i).length-1))+p := by simp [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_right edges _

private theorem floorBlockMass {a width : ℕ} (widthPos : 0 < width) (fits : width ≤ a) :
    a ≤ 2*((a/width)*width) := by
  have some : 0 < a/width := Nat.div_pos fits widthPos
  have raw := Nat.lt_mul_div_succ a widthPos
  have double : a/width+1 ≤ 2*(a/width) := by omega
  refine raw.le.trans ?_
  calc
    _ ≤ width*(2*(a/width)) := Nat.mul_le_mul_left width double
    _ = _ := by ring

/-- Directed complete bipartite blocks realize length two and uniform
degree width with the original budgets. -/
theorem frozen_cleaning_bipartite_rows {n p M width k : ℕ} (widthPos : 0 < width)
    (pPos : 0 < p) (vertexFits : 2*width ≤ n) (pathFits : width*width ≤ p)
    (massLow : p ≤ M) (massHigh : M ≤ 8*p)
    (degreeLow : M ≤ 4*(n*width)) (degreeFits : n*width ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let vertexBlocks := n/(2*width)
  let edgeBlocks := p/(width*width)
  let r := min vertexBlocks edgeBlocks
  let clean := frozenRectangleRows r width
  have nPos : 0 < n := (by positivity : 0 < 2*width).trans_le vertexFits
  have vFits : r*(2*width) ≤ n :=
    (Nat.mul_le_mul_right _ (min_le_left _ _)).trans (Nat.div_mul_le_self _ _)
  have pFits : r*(width*width) ≤ p :=
    (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  have mass : (∑ i, (clean i).length) = 2*(r*(width*width)) := by
    simp [clean,frozenRectangleRows,Nat.mul_comm]
  have retain : M ≤ 8*(2*(r*(width*width))) := by
    by_cases side : vertexBlocks ≤ edgeBlocks
    · have half : n ≤ 2*(r*(2*width)) := by
        rw [show r = vertexBlocks from min_eq_left side]
        exact floorBlockMass (by positivity) vertexFits
      calc
        _ ≤ 4*(n*width) := degreeLow
        _ ≤ 4*((2*(r*(2*width)))*width) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ half)
        _ = _ := by ring
    · have half : p ≤ 2*(r*(width*width)) := by
        rw [show r = edgeBlocks from min_eq_right (le_of_not_ge side)]
        exact floorBlockMass (by positivity) pathFits
      calc
        _ ≤ 8*p := massHigh
        _ ≤ _ := Nat.mul_le_mul_left _ half
  have upper : 2*(r*(width*width)) ≤ M := calc
    _ = (r*(2*width))*width := by ring
    _ ≤ n*width := Nat.mul_le_mul_right _ vFits
    _ ≤ _ := degreeFits
  refine ⟨_,vFits,_,pFits,clean,frozenRectangleRows_simple,frozenRectangleRows_free r width k,?_,?_,?_⟩
  · exact mass.symm ▸ retain
  · exact mass.symm ▸ upper
  · constructor
    · intro x
      rw [frozenRectangleRows_degree]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < (4:ℝ)*n)).mpr
        have cap : M ≤ width*(4*n) := by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using degreeLow
        exact_mod_cast cap
      · apply (le_div_iff₀ (by positivity : 0 < (n:ℝ))).mpr
        exact_mod_cast (show width*n ≤ 4*M by rw [Nat.mul_comm]; omega)
    · intro i
      have len : (clean i).length = 2 := by simp [clean,frozenRectangleRows]
      rw [len]
      norm_num only [Nat.cast_ofNat]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < (4:ℝ)*p)).mpr
        exact_mod_cast (show M ≤ 2*(4*p) by omega)
      · apply (le_div_iff₀ (by positivity : 0 < (p:ℝ))).mpr
        exact_mod_cast (show 2*p ≤ 4*M by omega)

private theorem rectangular_degree_bounds {n p M : ℕ} (hn : 0 < n) (order : n ≤ p)
    (large : 4*p < M) (small : M ≤ 8*p) (pairs : M ≤ n*(n-1)+p) :
    ∃ width, 0 < width ∧ 2*width ≤ n ∧ width*width ≤ p ∧ M ≤ 4*(n*width) ∧ n*width ≤ M := by
  have enough : 3*p < n*(n-1) := by omega
  have five : 5 ≤ n := by
    by_contra! low
    have four : n-1 ≤ 3 := by omega
    have pairsCap := Nat.mul_le_mul_left n four
    rw [Nat.mul_comm n 3] at pairsCap
    omega
  let width := (M+4*n-1)/(4*n)
  have den : 0 < 4*n := by positivity
  have positive : 0 < width := Nat.div_pos (by omega) den
  have cap : 4*(n*width) ≤ M+4*n-1 := by
    have bound := Nat.div_mul_le_self (M+4*n-1) (4*n)
    change width*(4*n) ≤ _ at bound
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bound
  have lower : M ≤ 4*(n*width) := by
    have bound := Nat.lt_mul_div_succ (M+4*n-1) den
    change M+4*n-1 < (4*n)*(width+1) at bound
    rw [Nat.mul_succ,Nat.mul_assoc] at bound
    omega
  have massFits : n*width ≤ M := by omega
  have tripleMass : 3*M ≤ 4*(n*(n-1)) := by omega
  have tripleWidth : 3*width ≤ n+1 := by
    have raw : (4*n)*(3*width) < (4*n)*(n+2) := calc
      _ = 3*(4*(n*width)) := by ring
      _ ≤ 3*(M+4*n-1) := Nat.mul_le_mul_left _ cap
      _ < 4*(n*(n-1))+12*n := by omega
      _ = (4*n)*(n+2) := by
        have rewrite : n+2 = (n-1)+3 := by omega
        rw [rewrite,Nat.mul_add,Nat.mul_assoc]
        ring
    have bound := (Nat.mul_lt_mul_left den).mp raw
    omega
  have vertexFits : 2*width ≤ n := by omega
  have widthCap : n*width+1 ≤ 2*p+n := by omega
  have demandFits : width*width ≤ p := by
    by_cases many : n+3 ≤ p
    · have n5 : (5 : ℝ) ≤ n := by exact_mod_cast five
      have pLower : (n : ℝ)+3 ≤ p := by exact_mod_cast many
      have width3 : 3*(width : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast tripleWidth
      have rhs : (n : ℝ)*(width : ℝ) ≤ 2*(p : ℝ)+(n : ℝ)-1 := by
        have cast : (n : ℝ)*(width : ℝ)+1 ≤ 2*(p : ℝ)+(n : ℝ) := by exact_mod_cast widthCap
        linarith only [cast]
      have poly : (n : ℝ)^2-1 ≤ ((n : ℝ)-2)*(p : ℝ) := calc
        _ ≤ ((n : ℝ)-2)*((n : ℝ)+3) := by nlinarith only [n5]
        _ ≤ _ := mul_le_mul_of_nonneg_left pLower (by linarith)
      have comparison : (3*(width : ℝ))*((n : ℝ)*(width : ℝ)) ≤ 3*(n : ℝ)*(p : ℝ) := calc
        _ ≤ ((n : ℝ)+1)*(2*(p : ℝ)+(n : ℝ)-1) := mul_le_mul width3 rhs (by positivity) (by positivity)
        _ ≤ _ := by nlinarith only [poly]
      have smallSquare : (width : ℝ)*(width : ℝ) ≤ p := by
        apply (mul_le_mul_iff_of_pos_left (by positivity : 0 < 3*(n : ℝ))).mp
        convert comparison using 1
        all_goals ring
      exact_mod_cast smallSquare
    · by_cases big : 9 ≤ n
      · have three : width ≤ 3 := by
          by_contra! widthLarge
          have lowerWidth := Nat.mul_le_mul_left n (show 4 ≤ width by omega)
          rw [Nat.mul_comm n 4] at lowerWidth
          omega
        exact (Nat.mul_le_mul three three).trans (by omega)
      · by_cases six : n ≤ 7
        · have two : width ≤ 2 := by omega
          exact (Nat.mul_le_mul two two).trans (by omega)
        · have eight : n = 8 := by omega
          by_cases haveNine : 9 ≤ p
          · have three : width ≤ 3 := by omega
            exact (Nat.mul_le_mul three three).trans haveNine
          · have only : p = 8 := by omega
            rw [eight,only] at widthCap
            have two : width ≤ 2 := by omega
            exact (Nat.mul_le_mul two two).trans (by omega)
  exact ⟨width,positive,vertexFits,demandFits,lower,massFits⟩

private theorem listMass_le_product {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) : (∑ i, (paths i).length) ≤ n*p := by
  calc
    _ ≤ ∑ _ : Fin p, n := by
      apply sum_le_sum
      intro i _
      rw [← List.toFinset_card_of_nodup (simple i)]
      simpa only [Fintype.card_fin] using (Finset.card_le_univ (paths i).toFinset)
    _ = n*p := by simp [Nat.mul_comm]

/-- If at most eight incidences per unit of the larger budget are needed,
one of the small witnesses meets the frozen caps. Full bridge exclusion in
the witness holds up to any requested output cutoff. -/
theorem regularization_list_frozen_low_mass_at_cutoff {n p k : ℕ} (outputCutoff : ℕ)
    (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (halfFree : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (low : (∑ i, (paths i).length) ≤ 8*max n p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) outputCutoff ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases sparse : M ≤ 4*max n p
  · exact full_frozen_cleaning_sparse_four hn hp dense long sparse
  · by_cases order : p ≤ n
    · apply frozen_cleaning_at_most_eight_per_vertex hp order dense
      · simpa only [max_eq_left order] using low
      · exact listMass_le_product paths simple
    · have other : n ≤ p := le_of_not_ge order
      have count : M ≤ n*(n-1)+p := listMass_le_ordered_pairs_add_paths paths simple halfFree cutoff
      have larger : 4*p < M := by
        rw [max_eq_right other] at sparse
        omega
      have smaller : M ≤ 8*p := by simpa only [max_eq_right other] using low
      obtain ⟨width,positive,vertices,demands,degree,fits⟩ :=
        rectangular_degree_bounds hn other larger smaller count
      exact frozen_cleaning_bipartite_rows positive hp vertices demands long smaller degree fits

/-- The low-mass witness with full exclusion at the input cutoff. -/
theorem regularization_list_frozen_low_mass {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (halfFree : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (low : (∑ i, (paths i).length) ≤ 8*max n p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_low_mass_at_cutoff k paths simple halfFree cutoff hn hp dense long low

/-- At any cutoff of at least two, an unrestricted maximum has a
frozen-cap witness in both bridge modes when either budget is at most eight. -/
theorem localOrderExtremal_frozen_small_side (n p k : ℕ) (half : Bool) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (small : min n p ≤ 8) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,legal,maximal,dense,long⟩ := localOrderExtremal_isDense n p k half hn hp
  have halfFree : HalfBridgeFree (ListBefore paths) k := by
    cases half
    · intro j small b _
      exact (legal small).false b
    · exact legal
  have fit := listMass_le_product paths simple
  have product : n*p = min n p * max n p := by
    by_cases order : n ≤ p
    · rw [min_eq_left order,max_eq_right order]
    · rw [min_eq_right (le_of_not_ge order),max_eq_left (le_of_not_ge order),Nat.mul_comm]
  have low : (∑ i, (paths i).length) ≤ 8*max n p := fit.trans (product ▸ Nat.mul_le_mul_right _ small)
  obtain ⟨n',v,p',i,clean,nodup,free,mass,upper,caps⟩ :=
    regularization_list_frozen_low_mass paths simple halfFree cutoff hn hp dense long low
  refine ⟨paths,simple,legal,maximal,n',v,p',i,clean,nodup,?_,mass,upper,caps⟩
  cases half
  · exact free
  · intro j small b _
    exact (free small).false b

/-- Use a small explicit witness at low mass, and original-width blocks
when a retained subsystem keeps at least seven eighths of a dense input. -/
theorem regularization_list_frozen_of_seven_eighths_mass {half : Bool} {k n p : ℕ}
    (paths kept : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (keptSimple : ∀ i, (kept i).Nodup)
    (halfFree : HalfBridgeFree (ListBefore paths) k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (upper : (∑ i, (kept i).length) ≤ ∑ i, (paths i).length)
    (lower : 8*max n p < (∑ i, (paths i).length) → 7*(∑ i, (paths i).length) ≤ 8*(∑ i, (kept i).length))
    (allowed : localOrderAdmissible half k (listRegularizedPaths kept
      (4*(∑ i, (paths i).length)/n) (4*(∑ i, (paths i).length)/p))) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',hn',p',hp',clean,simp,full,keeps,cap,caps⟩ :=
      regularization_list_frozen_low_mass paths simple halfFree cutoff hn hp dense long low
    have valid : localOrderAdmissible half k clean := by
      cases half
      · exact full
      · exact full.halfFree
    exact ⟨n',hn',p',hp',clean,simp,valid,keeps.trans (by omega),cap,caps⟩
  · have hnMass : 8*n ≤ M := (Nat.mul_le_mul_left _ (le_max_left _ _)).trans (Nat.le_of_lt (lt_of_not_ge low))
    have hpMass : 8*p ≤ M := (Nat.mul_le_mul_left _ (le_max_right _ _)).trans (Nat.le_of_lt (lt_of_not_ge low))
    exact regularization_list_frozen_after_large_width_blocks kept keptSimple allowed hn hp hnMass hpMass
      upper (lower (lt_of_not_ge low))

end OnlineReachabilityPreservers
