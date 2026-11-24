import DirectedFlowCutGap.VertexNormalizedPotentials
import DirectedFlowCutGap.RationalFourierMotzkin
import DirectedFlowCutGap.BinaryRawRational
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.ProdSigma

/-! Minimize the price of a normalized rational vertex assignment. Each demand
has its own potentials, and the common length variables charge only internal
vertices. The final coordinate is the objective minimized by elimination. -/
namespace DirectedFlowCutGap.NormalizedVertexLP

open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RationalSparsestVertexDistances (weights)
open RationalFourierMotzkin (Satisfies)

variable {m n : ℕ}

def dimension (n m : ℕ) : ℕ := n + m*n

def coordinates (n m : ℕ) : (Fin n ⊕ (Fin m × Fin n)) ≃ Fin (dimension n m) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv

def lengthIndex (v : Fin n) : Fin (dimension n m + 1) :=
  (coordinates n m (.inl v)).castSucc

def potentialIndex (i : Fin m) (v : Fin n) : Fin (dimension n m + 1) :=
  (coordinates n m (.inr (i,v))).castSucc

private def budgetIndex (n m : ℕ) : Fin (dimension n m + 1) := Fin.last (dimension n m)

private def row {k : ℕ} (constant : ℚ) (terms : List (Fin k × ℚ)) : RationalFourierMotzkin.Row k :=
  ⟨fun j => (terms.map fun (index,q) => if j = index then q else 0).sum,constant⟩

private theorem row_value {K : Type*} [Field K] [CharZero K] {k : ℕ} (constant : ℚ)
    (terms : List (Fin k × ℚ)) (x : Fin k → K) :
    (row constant terms).eval x =
      (constant : K) + (terms.map fun (index,q) => (q : K)*x index).sum := by
  unfold row RationalFourierMotzkin.Row.eval
  congr 1
  induction terms with
  | nil => simp
  | cons first tail ih =>
    rcases first with ⟨index,q⟩
    simp only [List.map_cons,List.sum_cons,Rat.cast_add,add_mul,Finset.sum_add_distrib,ih]
    congr 1
    simp only [apply_ite (fun t : ℚ => (t : K)),Rat.cast_zero,ite_mul,zero_mul,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private def arcs (A : Adjacency n) : List (Fin n × Fin n) :=
  (List.finRange n ×ˢ List.finRange n).filter fun e => A[e.1.val][e.2.val]

private theorem mem_arcs (A : Adjacency n) (e : Fin n × Fin n) :
    e ∈ arcs A ↔ (graph A).Adj e.1 e.2 := by
  rw [arcs,List.mem_filter]
  exact and_iff_right (List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩)

private def nonnegative {k : ℕ} (j : Fin k) : RationalFourierMotzkin.Row k := row 0 [(j,1)]

private def source (P : Fin m → Fin n × Fin n) (i : Fin m) :
    RationalFourierMotzkin.Row (dimension n m + 1) :=
  row 0 [(potentialIndex i (P i).1,-1)]

private def arc (P : Fin m → Fin n × Fin n) (i : Fin m) (e : Fin n × Fin n) :
    RationalFourierMotzkin.Row (dimension n m + 1) :=
  row 0 [(lengthIndex e.1,if e.1 = (P i).1 then 0 else 1),
    (potentialIndex i e.1,1),(potentialIndex i e.2,-1)]

private def targetRow (P : Fin m → Fin n × Fin n) (target : ℚ) :
    RationalFourierMotzkin.Row (dimension n m + 1) :=
  row (-target) ((List.finRange m).map fun i => (potentialIndex i (P i).2,1))

private def vertexPrice (c : Row n) (v : Fin n) : ℚ := (BinaryRational.decode (c.get v)).value

private def priceRow (m : ℕ) (c : Row n) : RationalFourierMotzkin.Row (dimension n m + 1) :=
  row 0 ((budgetIndex n m,1)::(List.finRange n).map fun v => (lengthIndex v,-vertexPrice c v))

def rows (A : Adjacency n) (c : Row n) (P : Fin m → Fin n × Fin n) (target : ℚ) :
    List (RationalFourierMotzkin.Row (dimension n m + 1)) :=
  ((List.finRange (dimension n m + 1)).map nonnegative) ++
    ((List.finRange m).map (source P)) ++
    ((List.finRange m).flatMap fun i => (arcs A).map (arc P i)) ++
    [targetRow P target, priceRow m c]

def lengthValue {K : Type*} (x : Fin (dimension n m + 1) → K) (v : Fin n) : K :=
  x (lengthIndex v)

def potential {K : Type*} (x : Fin (dimension n m + 1) → K) (i : Fin m) (v : Fin n) : K :=
  x (potentialIndex i v)

structure Constraints {K : Type*} [Field K] [Preorder K] (A : Adjacency n)
    (c : Row n) (P : Fin m → Fin n × Fin n) (target : ℚ)
    (x : Fin (dimension n m + 1) → K) : Prop where
  nonnegative : ∀ j, 0 ≤ x j
  origin : ∀ i, potential x i (P i).1 ≤ 0
  step : ∀ i (e : Fin n × Fin n), (graph A).Adj e.1 e.2 →
    potential x i e.2 ≤ potential x i e.1 + if e.1 = (P i).1 then 0 else lengthValue x e.1
  normalize : (target : K) ≤ ∑ i, potential x i (P i).2
  affordable : (∑ v, (vertexPrice c v : K)*lengthValue x v) ≤ x (budgetIndex n m)

section Evaluation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem nonnegative_value {k : ℕ} (x : Fin k → K) (j : Fin k) :
    0 ≤ (nonnegative j).eval x ↔ 0 ≤ x j := by
  simp [nonnegative,row_value]

private theorem source_value (P : Fin m → Fin n × Fin n) (x : Fin (dimension n m + 1) → K) (i : Fin m) :
    0 ≤ (source P i).eval x ↔ potential x i (P i).1 ≤ 0 := by
  simp [source,row_value,potential]

private theorem arc_value (P : Fin m → Fin n × Fin n) (x : Fin (dimension n m + 1) → K)
    (i : Fin m) (e : Fin n × Fin n) :
    0 ≤ (arc P i e).eval x ↔
      potential x i e.2 ≤ potential x i e.1 + if e.1 = (P i).1 then 0 else lengthValue x e.1 := by
  by_cases first : e.1 = (P i).1 <;>
    simp only [arc,row_value,Rat.cast_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      first,ite_true,ite_false,Rat.cast_one,Rat.cast_neg,one_mul,zero_mul,neg_mul,add_zero,zero_add,
      lengthValue,potential] <;>
    (constructor <;> intro h <;> linarith only [h])

private theorem target_value (P : Fin m → Fin n × Fin n) (target : ℚ)
    (x : Fin (dimension n m + 1) → K) :
    0 ≤ (targetRow P target).eval x ↔ (target : K) ≤ ∑ i, potential x i (P i).2 := by
  simp only [targetRow,row_value,List.map_map,Function.comp_def,Rat.cast_one,one_mul,Rat.cast_neg,potential]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
  constructor <;> intro h <;> linarith only [h]

private theorem price_value (c : Row n) (x : Fin (dimension n m + 1) → K) :
    0 ≤ (priceRow m c).eval x ↔
      (∑ v, (vertexPrice c v : K)*lengthValue x v) ≤ x (budgetIndex n m) := by
  simp only [priceRow,row_value,Rat.cast_zero,List.map_cons,List.sum_cons,Rat.cast_one,one_mul,
    zero_add,List.map_map,Function.comp_def,Rat.cast_neg,neg_mul,lengthValue]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange,Finset.sum_neg_distrib]
  constructor <;> intro h <;> linarith only [h]

theorem satisfies_iff (A : Adjacency n) (c : Row n) (P : Fin m → Fin n × Fin n)
    (target : ℚ) (x : Fin (dimension n m + 1) → K) :
    Satisfies (rows A c P target) x ↔ Constraints A c P target x := by
  constructor
  · intro all
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j
      apply (nonnegative_value x j).mp
      apply all
      simp only [rows,List.mem_append,List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨j,List.mem_finRange _,rfl⟩))
    · intro i
      apply (source_value P x i).mp
      apply all
      simp only [rows,List.mem_append,List.mem_map]
      exact Or.inl (Or.inl (Or.inr ⟨i,List.mem_finRange _,rfl⟩))
    · intro i e connected
      apply (arc_value P x i e).mp
      apply all
      simp only [rows,List.mem_append,List.mem_flatMap,List.mem_map]
      exact Or.inl (Or.inr ⟨i,List.mem_finRange _,e,(mem_arcs A e).mpr connected,rfl⟩)
    · apply (target_value P target x).mp
      apply all
      simp [rows]
    · apply (price_value c x).mp
      apply all
      simp [rows]
  · intro checks result inside
    simp only [rows,List.mem_append,List.mem_map,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with ((⟨j,_,rfl⟩ | ⟨i,_,rfl⟩) | ⟨i,_,e,member,rfl⟩) | (rfl | rfl)
    · exact (nonnegative_value x j).mpr (checks.nonnegative j)
    · exact (source_value P x i).mpr (checks.origin i)
    · exact (arc_value P x i e).mpr (checks.step i e ((mem_arcs A e).mp member))
    · exact (target_value P target x).mpr checks.normalize
    · exact (price_value c x).mpr checks.affordable

end Evaluation

def solutionLengths (x : Fin (dimension n m + 1) → ℚ) : Row n :=
  Vector.ofFn fun v =>
    (BinaryRawRational.encode (RawNonnegativeRational.Code.ofNNRat
      ⟨max (lengthValue x v) 0, le_max_right _ _⟩)).1

private theorem length_readback (x : Fin (dimension n m + 1) → ℚ)
    (nonnegative : ∀ j, 0 ≤ x j) (v : Fin n) :
    (weights (solutionLengths x) v : ℝ) = lengthValue (fun j => (x j : ℝ)) v := by
  rcases v with ⟨v,within⟩
  have h : 0 ≤ lengthValue x ⟨v,within⟩ := nonnegative (lengthIndex ⟨v,within⟩)
  have read : (BinaryRational.decode (solutionLengths x)[v]).value =
      (⟨max (lengthValue x ⟨v,within⟩) 0,le_max_right _ _⟩ : ℚ≥0) := by
    rw [solutionLengths,Vector.getElem_ofFn,BinaryRawRational.encode_value]
    exact RawNonnegativeRational.Code.value_ofNNRat _
  change (((BinaryRational.decode (solutionLengths x)[v]).value : ℝ≥0) : ℝ) = _
  rw [read]
  change ((max (lengthValue x ⟨v,within⟩) 0 : ℚ) : ℝ) = _
  rw [max_eq_left h]
  rfl

private theorem cost_sum (c : Row n) (w : Fin n → ℝ≥0)
    (x : Fin (dimension n m + 1) → ℝ) (given : ∀ v, lengthValue x v = (w v : ℝ)) :
    (∑ v, (vertexPrice c v : ℝ)*lengthValue x v) = (weightedCost (weights c) w : ℝ) := by
  simp only [weightedCost,NNReal.coe_sum,NNReal.coe_mul,given]
  rfl

def minimize (A : Adjacency n) (c : Row n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) : Option (ℚ × Row n) :=
  (RationalFourierMotzkin.minimizeLast (dimension n m) (rows A c P target)).map
    fun (q,x) => (q,solutionLengths x)

private theorem assignment_sound (A : Adjacency n) (c : Row n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    (x : Fin (dimension n m + 1) → ℚ) (rational : Satisfies (rows A c P target) x) :
    (target : ℝ≥0) ≤ ∑ i, SparsestVertexBridge.demandDistance (graph A) (weights (solutionLengths x)) (P i) ∧
      (weightedCost (weights c) (weights (solutionLengths x)) : ℝ) ≤ (x (budgetIndex n m) : ℝ) := by
  have nonnegative := ((satisfies_iff A c P target x).mp rational).nonnegative
  let y : Fin (dimension n m + 1) → ℝ := fun j => x j
  have real := RationalFourierMotzkin.rational_to_real (rows A c P target) x rational
  have fields := (satisfies_iff A c P target y).mp real
  let w := weights (solutionLengths x)
  let p (i : Fin m) (v : Fin n) : ℝ≥0 := ⟨potential y i v,fields.nonnegative (potentialIndex i v)⟩
  have fit : VertexNormalizedPotentials.Feasible (graph A) w P (target : ℝ≥0) p := by
    refine ⟨?_,?_,?_⟩
    · intro i
      apply NNReal.eq
      exact le_antisymm (fields.origin i) (p i (P i).1).coe_nonneg
    · intro i u v edge
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_add]
      change potential y i v ≤ potential y i u +
        (VertexNormalizedPotentials.departure w (P i).1 (u,v) : ℝ)
      have step := fields.step i (u,v) edge
      by_cases origin : u = (P i).1
      · rw [VertexNormalizedPotentials.departure,ite_eq_left origin,NNReal.coe_zero]
        simpa only [ite_eq_left origin] using step
      · rw [VertexNormalizedPotentials.departure,ite_eq_right origin,
          show (w u : ℝ) = lengthValue y u from length_readback x nonnegative u]
        simpa only [ite_eq_right origin] using step
    · apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_sum]
      exact fields.normalize
  have within := fields.affordable
  rw [cost_sum c w y (fun v => (length_readback x nonnegative v).symm)] at within
  exact ⟨(VertexNormalizedPotentials.normalization_iff (graph A) w P _ reachable).mp ⟨p,fit⟩,within⟩

private theorem comparison_assignment (A : Adjacency n) (c : Row n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (w : Fin n → ℝ≥0)
    (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    (normal : (target : ℝ≥0) ≤ ∑ i, SparsestVertexBridge.demandDistance (graph A) w (P i)) :
    ∃ x : Fin (dimension n m + 1) → ℝ,
      x (budgetIndex n m) = (weightedCost (weights c) w : ℝ) ∧
      Satisfies (rows A c P target) x := by
  obtain ⟨p,fit⟩ := (VertexNormalizedPotentials.normalization_iff (graph A) w P _ reachable).mpr normal
  let values (j : Fin (dimension n m)) : ℝ :=
    ((coordinates n m).symm j).elim (fun v => (w v : ℝ)) (fun (i,v) => (p i v : ℝ))
  let x : Fin (dimension n m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) values (weightedCost (weights c) w)
  have last : x (budgetIndex n m) = (weightedCost (weights c) w : ℝ) := Fin.snoc_last _ _
  have len (v : Fin n) : lengthValue x v = (w v : ℝ) := by
    simp only [x,lengthValue,lengthIndex,Fin.snoc_castSucc,values,Equiv.symm_apply_apply,Sum.elim_inl]
  have pot (i : Fin m) (v : Fin n) : potential x i v = (p i v : ℝ) := by
    simp only [x,potential,potentialIndex,Fin.snoc_castSucc,values,Equiv.symm_apply_apply,Sum.elim_inr]
  refine ⟨x,last,(satisfies_iff A c P target x).mpr ⟨?_,?_,?_,?_,?_⟩⟩
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [show Fin.last (dimension n m) = budgetIndex n m from rfl,last]
      positivity
    · rw [show x k.castSucc = values k from Fin.snoc_castSucc ..]
      unfold values
      cases (coordinates n m).symm k with
      | inl v => exact (w v).coe_nonneg
      | inr iv => exact (p iv.1 iv.2).coe_nonneg
  · intro i
    rw [pot,fit.origin i,NNReal.coe_zero]
  · intro i e edge
    rw [pot,pot,len]
    have step := NNReal.coe_le_coe.mpr (fit.step i e.1 e.2 edge)
    rw [NNReal.coe_add] at step
    by_cases origin : e.1 = (P i).1 <;>
      simpa only [VertexNormalizedPotentials.departure,origin,ite_true,ite_false,NNReal.coe_zero] using step
  · simp only [pot]
    exact_mod_cast fit.normalize
  · rw [cost_sum c w x len,last]

theorem minimize_complete (A : Adjacency n) (c : Row n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (w : Fin n → ℝ≥0)
    (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    (normal : (target : ℝ≥0) ≤ ∑ i, SparsestVertexBridge.demandDistance (graph A) w (P i)) :
    (minimize A c P target).isSome := by
  obtain ⟨x,last,fit⟩ := comparison_assignment A c P target w reachable normal
  have nonnegative : 0 ≤ x (Fin.last (dimension n m)) := by
    change 0 ≤ x (budgetIndex n m)
    rw [last]
    positivity
  unfold minimize
  rw [Option.isSome_map]
  exact RationalFourierMotzkin.minimizeLast_complete _ _ x nonnegative fit

theorem minimize_attained (A : Adjacency n) (c : Row n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    {q : ℚ} {w : Row n} (returned : minimize A c P target = some (q,w)) :
    (target : ℝ≥0) ≤ ∑ i, SparsestVertexBridge.demandDistance (graph A) (weights w) (P i) ∧
      (weightedCost (weights c) (weights w) : ℝ) = (q : ℝ) ∧
      ∀ other : Fin n → ℝ≥0,
        (target : ℝ≥0) ≤ ∑ i, SparsestVertexBridge.demandDistance (graph A) other (P i) →
          (q : ℝ) ≤ (weightedCost (weights c) other : ℝ) := by
  obtain ⟨⟨best,x⟩,solved,same⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  obtain ⟨_,last,fit⟩ := RationalFourierMotzkin.minimizeLast_sound _ _ solved
  obtain ⟨normal,within⟩ := assignment_sound A c P target reachable x fit
  change x (budgetIndex n m) = best at last
  rw [last] at within
  have least (other : Fin n → ℝ≥0)
      (good : (target : ℝ≥0) ≤ ∑ i, SparsestVertexBridge.demandDistance (graph A) other (P i)) :
      (best : ℝ) ≤ (weightedCost (weights c) other : ℝ) := by
    obtain ⟨y,objective,valid⟩ := comparison_assignment A c P target other reachable good
    change y (Fin.last (dimension n m)) = _ at objective
    have nonnegative : 0 ≤ y (Fin.last (dimension n m)) := by rw [objective]; positivity
    rw [← objective]
    exact RationalFourierMotzkin.minimizeLast_optimal _ _ solved y nonnegative valid
  exact ⟨normal,le_antisymm within (least _ normal),least⟩

end DirectedFlowCutGap.NormalizedVertexLP
