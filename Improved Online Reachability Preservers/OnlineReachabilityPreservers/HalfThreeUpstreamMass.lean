import OnlineReachabilityPreservers.CyclicIntersections
import OnlineReachabilityPreservers.OppositeIntersectionPruning
import Mathlib.Analysis.Real.Sqrt

/-! Upstream vertices of later branches give an incidence bound at half cutoff three. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem same_later_branch_of_shared_upstream {n p k : ℕ} {paths : Fin p → List (Fin n)}
    (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    {i j j' : Fin p} (earlier : i < j) (earlier' : i < j') {x x' u : Fin n}
    (hit : x ∈ paths i) (hit' : x' ∈ paths i)
    (up : Before paths j u x) (up' : Before paths j' u x') : j = j' := by
  by_contra different
  by_cases equal : x = x'
  · subst x'
    exact no_parallel_list_steps free (by omega) different up up'
  rcases listBefore_total hit hit' equal with along | against
  · let bridge := threeListBridge earlier.ne' (fun equal => different equal.symm) earlier'.ne' up along up'
    exact free three bridge earlier'
  · let bridge := threeListBridge earlier'.ne' different earlier.ne' up' against up
    exact free three bridge earlier

private abbrev rowIncidences {n p : ℕ} (paths : Fin p → List (Fin n)) : Finset (Fin p × Fin n) :=
  univ.filter (fun v => v.2 ∈ paths v.1)

private theorem rowIncidences_card {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) : (rowIncidences paths).card = ∑ i, (paths i).length := by
  have count := card_eq_sum_card_fiberwise (s := rowIncidences paths) (t := (univ : Finset (Fin p)))
    (f := Prod.fst) (fun x _ => mem_univ x.1)
  rw [count]
  apply sum_congr rfl
  intro i _
  let withRow : Fin n ↪ Fin p × Fin n := ⟨Prod.mk i,fun _ _ equal => congrArg Prod.snd equal⟩
  have exactFiber : (rowIncidences paths).filter (fun x => x.1 = i) = (paths i).toFinset.map withRow := by
    ext x
    rcases x with ⟨j,v⟩
    simp only [rowIncidences,mem_filter,mem_univ,true_and,mem_map,List.mem_toFinset]
    constructor
    · rintro ⟨on,rfl⟩
      exact ⟨v,on,rfl⟩
    · rintro ⟨w,on,equal⟩
      change (i,w) = (j,v) at equal
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      exact ⟨on,rfl⟩
  rw [exactFiber,card_map,List.toFinset_card_of_nodup (simple i)]

private abbrev arrivalPredecessors {n p : ℕ} (paths : Fin p → List (Fin n)) (i : Fin p) (x : Fin n) :=
  predecessors (occurrences (fun i => (paths i).toFinset) x) i

private theorem mem_arrivalPredecessors {n p : ℕ} {paths : Fin p → List (Fin n)} {i j : Fin p} {x : Fin n} :
    j ∈ arrivalPredecessors paths i x ↔ x ∈ paths j ∧ j < i := by
  simp [arrivalPredecessors,predecessors,mem_occurrences]

private theorem small_row_position_count {n p : ℕ} (paths : Fin p → List (Fin n)) (L : ℕ) :
    ((rowIncidences paths).filter (fun v => (paths v.1).idxOf v.2 < L)).card ≤ p*L := by
  let S := (rowIncidences paths).filter (fun v => (paths v.1).idxOf v.2 < L)
  let rank (x : S) : Fin p × Fin L := (x.val.1,⟨(paths x.val.1).idxOf x.val.2,(mem_filter.mp x.property).2⟩)
  have injective : Function.Injective rank := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ equal
    obtain rfl : i = j := congrArg Prod.fst equal
    have on : x ∈ paths i := (mem_filter.mp (mem_filter.mp hx).1).2
    have idx : (paths i).idxOf x = (paths i).idxOf y := congrArg (fun a => a.2.val) equal
    obtain rfl := (List.idxOf_inj on).mp idx
    rfl
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective rank injective

private theorem small_arrival_rank_count {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) :
    ((rowIncidences paths).filter (fun v => (arrivalPredecessors paths v.1 v.2).card < D)).card ≤ n*D := by
  let S := (rowIncidences paths).filter (fun v => (arrivalPredecessors paths v.1 v.2).card < D)
  let rank (x : S) : Fin n × Fin D := (x.val.2,⟨(arrivalPredecessors paths x.val.1 x.val.2).card,(mem_filter.mp x.property).2⟩)
  have injective : Function.Injective rank := by
    rintro ⟨⟨i,x⟩,hx⟩ ⟨⟨j,y⟩,hy⟩ equal
    obtain rfl : x = y := congrArg Prod.fst equal
    have hx' : i ∈ occurrences (fun a => (paths a).toFinset) x := by
      exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_filter.mp (mem_filter.mp hx).1).2)
    have hy' : j ∈ occurrences (fun a => (paths a).toFinset) x := by
      exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_filter.mp (mem_filter.mp hy).1).2)
    have idx : (arrivalPredecessors paths i x).card = (arrivalPredecessors paths j x).card :=
      congrArg (fun a => a.2.val) equal
    obtain rfl := predecessor_count_injective _ hx' hy' idx
    rfl
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective rank injective

private abbrev lateIncidences {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) :=
  (rowIncidences paths).filter (fun v => D ≤ (arrivalPredecessors paths v.1 v.2).card ∧ L ≤ (paths v.1).idxOf v.2)

private theorem lateIncidences_card_lower {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (D L : ℕ) :
    (∑ i, (paths i).length) ≤ (lateIncidences paths D L).card+n*D+p*L := by
  let early := (rowIncidences paths).filter (fun v => (arrivalPredecessors paths v.1 v.2).card < D)
  let front := (rowIncidences paths).filter (fun v => (paths v.1).idxOf v.2 < L)
  let good := lateIncidences paths D L
  have cover : rowIncidences paths ⊆ (good ∪ early) ∪ front := by
    intro v on
    by_cases a : (arrivalPredecessors paths v.1 v.2).card < D
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨on,a⟩ : v ∈ early))
    by_cases b : (paths v.1).idxOf v.2 < L
    · exact mem_union_right _ (mem_filter.mpr ⟨on,b⟩ : v ∈ front)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨on,le_of_not_gt a,le_of_not_gt b⟩ : v ∈ good))
  rw [← rowIncidences_card paths simple]
  calc
    _ ≤ ((good ∪ early) ∪ front).card := card_le_card cover
    _ ≤ (good ∪ early).card+front.card := card_union_le _ _
    _ ≤ (good.card+early.card)+front.card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add_left (small_arrival_rank_count paths D) _) (small_row_position_count paths L)

private theorem lateIncidences_mul_le {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (D L : ℕ) : (lateIncidences paths D L).card*D*L ≤ p*n := by
  classical
  let S := lateIncidences paths D L
  have present (s : S) : s.val.2 ∈ paths s.val.1 := (mem_filter.mp (mem_filter.mp s.property).1).2
  have earlierCount (s : S) : D ≤ (arrivalPredecessors paths s.val.1 s.val.2).card := (mem_filter.mp s.property).2.1
  have position (s : S) : L ≤ (paths s.val.1).idxOf s.val.2 := (mem_filter.mp s.property).2.2
  let chooseBase (s : S) : Fin D ↪ (arrivalPredecessors paths s.val.1 s.val.2) :=
    (Fin.castLEEmb (earlierCount s)).trans (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm.toEmbedding
  let up (s : S) (offset : Fin L) : Fin n :=
    (paths s.val.1)[offset.val]'((offset.isLt.trans_le (position s)).trans (List.idxOf_lt_length_of_mem (present s)))
  have upStep (s : S) (offset : Fin L) : Before paths s.val.1 (up s offset) s.val.2 := by
    refine ⟨List.getElem_mem _,present s,?_⟩
    dsimp only [up]
    rw [(simple s.val.1).idxOf_getElem]
    exact offset.isLt.trans_le (position s)
  let image (x : S × Fin D × Fin L) : Fin p × Fin n := ((chooseBase x.1 x.2.1).val,up x.1 x.2.2)
  have injective : Function.Injective image := by
    rintro ⟨a,d,l⟩ ⟨b,e,m⟩ equal
    let i := (chooseBase a d).val
    have matchBase : i = (chooseBase b e).val := congrArg Prod.fst equal
    have matchUp : up a l = up b m := congrArg Prod.snd equal
    obtain ⟨onA,beforeA⟩ := mem_arrivalPredecessors.mp (chooseBase a d).property
    have bBase : i ∈ arrivalPredecessors paths b.val.1 b.val.2 := matchBase.symm ▸ (chooseBase b e).property
    obtain ⟨onB,beforeB⟩ := mem_arrivalPredecessors.mp bBase
    have tail : a.val.1 = b.val.1 := same_later_branch_of_shared_upstream free three beforeA beforeB
      onA onB (upStep a l) (matchUp.symm ▸ upStep b m)
    have hit : a.val.2 = b.val.2 := unique beforeA.ne onA (present a) onB (tail.symm ▸ present b)
    have incidence : a = b := Subtype.ext (Prod.ext tail hit)
    subst b
    have baseEq : d = e := (chooseBase a).injective (Subtype.ext matchBase)
    have indices := congrArg (paths a.val.1).idxOf matchUp
    dsimp only [up] at indices
    rw [(simple a.val.1).idxOf_getElem,(simple a.val.1).idxOf_getElem] at indices
    have posEq : l = m := Fin.ext indices
    exact Prod.ext rfl (Prod.ext baseEq posEq)
  have bound := Fintype.card_le_of_injective image injective
  simpa only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.mul_assoc] using bound

private theorem average_quarter_bounds {M a : ℕ} (positive : 0 < a) (large : 4*a ≤ M) :
    let D := M/(4*a)
    4*(a*D) ≤ M ∧ M ≤ 8*a*D := by
  let D := M/(4*a)
  have divisor : 0 < 4*a := by positivity
  have DPos : 1 ≤ D := Nat.le_div_iff_mul_le divisor |>.mpr (by simpa using large)
  constructor
  · simpa only [← Nat.mul_assoc] using Nat.mul_div_le M (4*a)
  · calc
      M ≤ (4*a)*(D+1) := (Nat.lt_mul_div_succ _ divisor).le
      _ ≤ (4*a)*(2*D) := Nat.mul_le_mul_left _ (by omega)
      _ = (8*a)*D := by ring

/-- A simple half-three-free family has either at most `8(n+p)` mass
or mass with cube at most `1024 (np)^2`. Every larger half cutoff inherits
the bound. No regularity hypothesis on the input is needed. -/
theorem half_three_mass_cubic_or_linear {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    let M := ∑ i, (paths i).length
    M ≤ 8*(n+p) ∨ M^3 ≤ 1024*(n*p)^2 := by
  let M₀ := ∑ i, (paths i).length
  by_cases small : M₀ ≤ 8*(n+p)
  · exact Or.inl small
  apply Or.inr
  have hn : 0 < n := by
    by_contra! zero
    have nil (i : Fin p) : paths i = [] := List.eq_nil_iff_forall_not_mem.mpr
      (fun v _ => (Nat.not_lt_of_ge zero) ((Nat.zero_le v.val).trans_lt v.isLt))
    simp [M₀,nil] at small
  have hp : 0 < p := by
    by_contra! zero
    have pZero : p = 0 := by omega
    have none : IsEmpty (Fin p) := pZero ▸ (inferInstance : IsEmpty (Fin 0))
    simp [M₀,Finset.univ_eq_empty] at small
  let rows := removeOppositeIntersections paths
  let M := ∑ i, (rows i).length
  have keep : M₀ ≤ 2*M := removeOppositeIntersections_mass simple free three
  have rowsSimple (i : Fin p) : (rows i).Nodup := (removeOppositeIntersections_sublist paths i).nodup (simple i)
  let D := M/(4*n)
  let L := M/(4*p)
  let G := (lateIncidences rows D L).card
  have bigN : 4*n ≤ M := by omega
  have bigP : 4*p ≤ M := by omega
  obtain ⟨degreeBudget,degree⟩ := average_quarter_bounds hn bigN
  obtain ⟨positionBudget,position⟩ := average_quarter_bounds hp bigP
  change 4*(n*D) ≤ M at degreeBudget
  change M ≤ 8*n*D at degree
  change 4*(p*L) ≤ M at positionBudget
  change M ≤ 8*p*L at position
  have incidence := lateIncidences_card_lower rows rowsSimple D L
  change M ≤ G+n*D+p*L at incidence
  have many : M ≤ 2*G := by omega
  have pack : G*D*L ≤ p*n := lateIncidences_mul_le rows rowsSimple (removeOppositeIntersections_halfFree simple free)
    three (fun {_ _ _ _} apart xa xb ya yb => removeOppositeIntersections_unique simple free (by omega) apart xa xb ya yb) D L
  change M₀^3 ≤ 1024*(n*p)^2
  calc
    _ ≤ (2*M)^3 := Nat.pow_le_pow_left keep 3
    _ = 8*(M*M*M) := by ring
    _ ≤ 8*((2*G)*(8*n*D)*(8*p*L)) := Nat.mul_le_mul_left 8 (Nat.mul_le_mul (Nat.mul_le_mul many degree) position)
    _ = 1024*(G*D*L)*(n*p) := by ring
    _ ≤ 1024*(p*n)*(n*p) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ pack)
    _ = _ := by ring

/-- At unbounded path budgets, half-three mass of order `n √p` requires
a positive quadratic path density. The constants depend only on the
mass fraction, so the statement also applies at every larger cutoff. -/
theorem half_three_n_sqrt_p_mass_requires_quadratic_path_density (η : ℝ) (positive : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 0 < P ∧ ∀ {n p k : ℕ}, 0 < n → P ≤ p → 3 ≤ k →
      ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) → HalfBridgeFree (Before paths) k →
      η*(n:ℝ)*Real.sqrt p ≤ ((∑ i, (paths i).length : ℕ):ℝ) → δ*(n:ℝ)^2 ≤ p := by
  let t := min (η/16) (η^3/1024)
  have tPos : 0 < t := lt_min (by positivity) (by positivity)
  refine ⟨t^2,by positivity,⌈(16/η)^2⌉₊+1,by positivity,?_⟩
  intro n p k hn large three paths simple free dense
  let y := Real.sqrt (p:ℝ)
  have pPos : 0 < p := by omega
  have yPos : 0 < y := Real.sqrt_pos.mpr (Nat.cast_pos.mpr pPos)
  have nPos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have square : y^2 = (p:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have rootBound : t*(n:ℝ) ≤ y := by
    rcases half_three_mass_cubic_or_linear paths simple free three with linear | cube
    · have threshold : (16/η)^2 ≤ (p:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
      have base : 16/η ≤ y := (sq_le_sq₀ (by positivity) yPos.le).mp (square ▸ threshold)
      have scaleN : (16:ℝ) ≤ η*y := by simpa only [mul_comm] using (div_le_iff₀ positive).mp base
      have costN : (8:ℝ)*n ≤ (η/2)*(n:ℝ)*y := by
        have price := mul_le_mul_of_nonneg_right scaleN nPos.le
        linarith only [price]
      by_contra! sparse
      have smallP : y < (η/16)*(n:ℝ) := sparse.trans_le
        (mul_le_mul_of_nonneg_right (min_le_left _ _) nPos.le)
      have costP : (8:ℝ)*p < (η/2)*(n:ℝ)*y := by
        have price := mul_lt_mul_of_pos_right smallP yPos
        rw [← square]
        linarith only [price]
      have mass : ((∑ i, (paths i).length : ℕ):ℝ) ≤ 8*((n:ℝ)+p) := by exact_mod_cast linear
      linarith only [mass,dense,costN,costP]
    · have cap : ((∑ i, (paths i).length : ℕ):ℝ)^3 ≤ 1024*((n:ℝ)*p)^2 := by exact_mod_cast cube
      have product : (η^3*(n:ℝ))*((n:ℝ)^2*y^3) ≤ (1024*y)*((n:ℝ)^2*y^3) := calc
        _ = (η*(n:ℝ)*y)^3 := by ring
        _ ≤ ((∑ i, (paths i).length : ℕ):ℝ)^3 := pow_le_pow_left₀ (by positivity) dense 3
        _ ≤ 1024*((n:ℝ)*p)^2 := cap
        _ = 1024*((n:ℝ)*y^2)^2 := by rw [square]
        _ = _ := by ring
      have scale : η^3*(n:ℝ) ≤ 1024*y := le_of_mul_le_mul_right product (by positivity)
      calc
        _ ≤ (η^3/1024)*(n:ℝ) := mul_le_mul_of_nonneg_right (min_le_right _ _) nPos.le
        _ ≤ y := by linarith only [scale]
  calc
    _ = (t*(n:ℝ))^2 := by ring
    _ ≤ y^2 := pow_le_pow_left₀ (by positivity) rootBound 2
    _ = _ := square

end OnlineReachabilityPreservers
