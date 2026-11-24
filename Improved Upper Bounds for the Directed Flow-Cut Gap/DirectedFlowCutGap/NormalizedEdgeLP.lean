import DirectedFlowCutGap.SparsestNormalizedPotentials
import DirectedFlowCutGap.RationalFourierMotzkin
import DirectedFlowCutGap.BinaryRawRational
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.ProdSigma

/-! Generate the finite rational linear constraints for a budgeted normalized
fractional edge assignment. One variable per matrix position and per
demand/vertex replaces the family of path constraints. -/
namespace DirectedFlowCutGap.NormalizedEdgeLP

open scoped BigOperators NNRat NNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalFourierMotzkin (Row Satisfies)

def dimension (n m : ℕ) : ℕ := n*n+m*n

def coordinates (n m : ℕ) :
    ((Fin n × Fin n) ⊕ (Fin m × Fin n)) ≃ Fin (dimension n m) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

def weightIndex {n m : ℕ} (edge : Fin n × Fin n) : Fin (dimension n m) :=
  coordinates n m (.inl edge)

def potentialIndex {n m : ℕ} (i : Fin m) (v : Fin n) : Fin (dimension n m) :=
  coordinates n m (.inr (i,v))

private def coefficient {k : ℕ} (j : Fin k) (entry : Fin k × ℚ) : ℚ :=
  if j=entry.1 then entry.2 else 0

private def row {k : ℕ} (constant : ℚ) (terms : List (Fin k × ℚ)) : Row k :=
  ⟨fun j => (terms.map (coefficient j)).sum,constant⟩

private theorem evaluated {K : Type*} [Field K] [CharZero K] {k : ℕ} (constant : ℚ)
    (terms : List (Fin k × ℚ)) (x : Fin k → K) :
    (row constant terms).eval x =
      (constant : K)+(terms.map (fun entry => (entry.2 : K)*x entry.1)).sum := by
  unfold row Row.eval
  congr 1
  induction terms with
  | nil => simp
  | cons first later ih =>
    simp only [List.map_cons,List.sum_cons,Rat.cast_add,add_mul,Finset.sum_add_distrib,ih]
    congr 1
    simp only [coefficient,apply_ite (fun q : ℚ => (q : K)),Rat.cast_zero,ite_mul,zero_mul,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private def arcs {n : ℕ} (A : Adjacency n) : List (Fin n × Fin n) :=
  (List.finRange n ×ˢ List.finRange n).filter fun e => A[e.1.val][e.2.val]

private theorem mem_arcs {n : ℕ} (A : Adjacency n) (e : Fin n × Fin n) :
    e ∈ arcs A ↔ (graph A).Adj e.1 e.2 := by
  rw [arcs,List.mem_filter]
  exact and_iff_right (List.mem_product.mpr ⟨List.mem_finRange _,List.mem_finRange _⟩)

private theorem arc_count {n : ℕ} (A : Adjacency n) : (arcs A).length≤n*n := by
  have all : (List.finRange n ×ˢ List.finRange n).length=n*n := by
    simpa only [List.length_finRange] using List.length_product (List.finRange n) (List.finRange n)
  have filtered := List.length_filter_le (fun e : Fin n × Fin n => A[e.1.val][e.2.val])
    (List.finRange n ×ˢ List.finRange n)
  exact filtered.trans_eq all

private def nonnegative {k : ℕ} (j : Fin k) : Row k := row 0 [(j,1)]

private def source {m n : ℕ} (P : Fin m → Fin n × Fin n) (i : Fin m) : Row (dimension n m) :=
  row 0 [(potentialIndex i (P i).1,-1)]

private def arc {m n : ℕ} (i : Fin m) (e : Fin n × Fin n) : Row (dimension n m) :=
  row 0 [(weightIndex e,1),(potentialIndex i e.1,1),(potentialIndex i e.2,-1)]

def normalization {m n : ℕ} (P : Fin m → Fin n × Fin n) (target : ℚ) : Row (dimension n m) :=
  row (-target) ((List.finRange m).map fun i => (potentialIndex i (P i).2,1))

private def cost {n : ℕ} (c : Weights n) (e : Fin n × Fin n) : ℚ :=
  (BinaryRational.decode ((c.get e.1).get e.2)).value

def price (n m : ℕ) (A : Adjacency n) (c : Weights n) (budget : ℚ) : Row (dimension n m) :=
  row budget ((arcs A).map fun e => (weightIndex e,-cost c e))

def rows {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target budget : ℚ) : List (Row (dimension n m)) :=
  ((List.finRange (dimension n m)).map nonnegative) ++
    ((List.finRange m).map (source P)) ++
    ((List.finRange m).flatMap fun i => (arcs A).map (arc i)) ++
    [normalization P target,price n m A c budget]

theorem rows_length {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target budget : ℚ) : (rows A c P target budget).length≤dimension n m+m+m*(n*n)+2 := by
  have positions := arc_count A
  simp only [rows,List.length_append,List.length_map,List.length_finRange,List.length_cons,List.length_nil,
    List.length_flatMap,List.map_const',List.sum_replicate]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left m positions) _) _

def weightValues {K : Type*} {n m : ℕ} (x : Fin (dimension n m) → K) (e : Fin n × Fin n) : K :=
  x (weightIndex e)

def potentialValues {K : Type*} {n m : ℕ} (x : Fin (dimension n m) → K) (i : Fin m) (v : Fin n) : K :=
  x (potentialIndex i v)

structure Constraints {K : Type*} [Field K] [Preorder K] {m n : ℕ} (A : Adjacency n)
    (c : Weights n) (P : Fin m → Fin n × Fin n) (target budget : ℚ)
    (x : Fin (dimension n m) → K) : Prop where
  nonnegative : ∀ j, 0≤x j
  origin : ∀ i, potentialValues x i (P i).1≤0
  step : ∀ i e, (graph A).Adj e.1 e.2 →
    potentialValues x i e.2≤potentialValues x i e.1+weightValues x e
  normalize : (target : K)≤∑ i, potentialValues x i (P i).2
  affordable : ((arcs A).map (fun e => (cost c e : K)*weightValues x e)).sum≤(budget : K)

section Evaluation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}

private theorem nonnegative_value {k : ℕ} (x : Fin k → K) (j : Fin k) :
    0≤(nonnegative j).eval x ↔ 0≤x j := by
  simp [nonnegative,evaluated]

private theorem source_value (P : Fin m → Fin n × Fin n) (x : Fin (dimension n m) → K) (i : Fin m) :
    0≤(source P i).eval x ↔ potentialValues x i (P i).1≤0 := by
  simp [source,evaluated,potentialValues]

private theorem arc_value (x : Fin (dimension n m) → K) (i : Fin m) (e : Fin n × Fin n) :
    0≤(arc i e).eval x ↔ potentialValues x i e.2≤potentialValues x i e.1+weightValues x e := by
  simp only [arc,evaluated,Rat.cast_zero,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Rat.cast_one,Rat.cast_neg,one_mul,neg_mul,add_zero,zero_add,weightValues,potentialValues]
  constructor <;> intro h <;> linarith

private theorem normalized_value (P : Fin m → Fin n × Fin n) (target : ℚ) (x : Fin (dimension n m) → K) :
    0≤(normalization P target).eval x ↔ (target : K)≤∑ i, potentialValues x i (P i).2 := by
  simp only [normalization,evaluated,List.map_map,Function.comp_def,Rat.cast_one,one_mul,Rat.cast_neg,potentialValues]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]
  constructor <;> intro h <;> linarith

private theorem price_eval (A : Adjacency n) (c : Weights n) (budget : ℚ) (x : Fin (dimension n m) → K) :
    (price n m A c budget).eval x=(budget : K)-((arcs A).map (fun e => (cost c e : K)*weightValues x e)).sum := by
  let fees := (arcs A).map (fun e => (cost c e : K)*weightValues x e)
  simp only [price,evaluated,List.map_map,Function.comp_def,Rat.cast_neg,neg_mul]
  have negated : (fees.map Neg.neg)=(arcs A).map fun e => -((cost c e : K)*x (weightIndex e)) := by
    simp only [fees,List.map_map,Function.comp_def,weightValues]
  rw [←negated]
  have negate (s : List K) : (s.map Neg.neg).sum= -s.sum := by
    induction s with
    | nil => simp
    | cons first rest ih => simp only [List.map_cons,List.sum_cons,ih,neg_add]
  rw [negate fees,sub_eq_add_neg]

private theorem price_value (A : Adjacency n) (c : Weights n) (budget : ℚ) (x : Fin (dimension n m) → K) :
    0≤(price n m A c budget).eval x ↔
      ((arcs A).map (fun e => (cost c e : K)*weightValues x e)).sum≤(budget : K) := by
  rw [price_eval,sub_nonneg]

theorem satisfies_iff (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target budget : ℚ) (x : Fin (dimension n m) → K) :
    Satisfies (rows A c P target budget) x ↔ Constraints A c P target budget x := by
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
      apply (arc_value x i e).mp
      apply all
      simp only [rows,List.mem_append,List.mem_flatMap,List.mem_map]
      exact Or.inl (Or.inr ⟨i,List.mem_finRange _,e,(mem_arcs A e).mpr connected,rfl⟩)
    · apply (normalized_value P target x).mp
      apply all
      simp [rows]
    · apply (price_value A c budget x).mp
      apply all
      simp [rows]
  · intro checks result inside
    simp only [rows,List.mem_append,List.mem_map,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with ((⟨j,_,rfl⟩ | ⟨i,_,rfl⟩) | ⟨i,_,e,member,rfl⟩) | (rfl | rfl)
    · exact (nonnegative_value x j).mpr (checks.nonnegative j)
    · exact (source_value P x i).mpr (checks.origin i)
    · exact (arc_value x i e).mpr (checks.step i e ((mem_arcs A e).mp member))
    · exact (normalized_value P target x).mpr checks.normalize
    · exact (price_value A c budget x).mpr checks.affordable

end Evaluation

private theorem arcs_nodup {n : ℕ} (A : Adjacency n) : (arcs A).Nodup :=
  ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _

private theorem arcs_set {n : ℕ} (A : Adjacency n) : (arcs A).toFinset=graphEdges (graph A) := by
  ext e
  rw [List.mem_toFinset,mem_arcs,mem_graphEdges]

private theorem price_sum {n m : ℕ} (A : Adjacency n) (c : Weights n)
    (w : Fin n × Fin n → ℝ≥0) (x : Fin (dimension n m) → ℝ) (given : ∀ e, weightValues x e=(w e : ℝ)) :
    ((arcs A).map (fun e => (cost c e : ℝ)*weightValues x e)).sum=
      (weightedEdgeCost (graph A) (weights c) w : ℝ) := by
  rw [←List.sum_toFinset _ (arcs_nodup A),arcs_set,weightedEdgeCost,NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [given,NNReal.coe_mul]
  rfl

def solve {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (budget : ℚ) : Option (Fin (dimension n m) → ℚ) :=
  RationalFourierMotzkin.solve (dimension n m) (rows A c P (target : ℚ) budget)

private def nonnegativeRat (q : ℚ) : ℚ≥0 := ⟨max q 0,le_max_right _ _⟩

def solutionWeights {m n : ℕ} (x : Fin (dimension n m) → ℚ) : Weights n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    (BinaryRawRational.encode
      (RawNonnegativeRational.Code.ofNNRat (nonnegativeRat (weightValues x (u,v))))).1

private theorem weight_readback {m n : ℕ} (x : Fin (dimension n m) → ℚ)
    (nonnegative : ∀ j, 0≤x j) (e : Fin n × Fin n) :
    (weights (solutionWeights x) e : ℝ)=weightValues (fun j => (x j : ℝ)) e := by
  rcases e with ⟨u,v⟩
  have h : 0≤weightValues x (u,v) := nonnegative (weightIndex (u,v))
  simp only [weights,RationalEdgeThresholds.cost,BinaryFractionalWalkOracle.decodeCost,
    solutionWeights,Vector.getElem_ofFn,BinaryRawRational.encode_value,RawNonnegativeRational.Code.value_ofNNRat]
  change ((max (weightValues x (u,v)) 0 : ℚ) : ℝ)=_
  rw [max_eq_left h]
  rfl

def findWeights {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (budget : ℚ) : Option (Weights n) :=
  (solve A c P target budget).map solutionWeights

private theorem assignment_sound {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (budget : ℚ)
    (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2)) (x : Fin (dimension n m) → ℚ)
    (rational : Satisfies (rows A c P (target : ℚ) budget) x) :
    (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) (weights (solutionWeights x)) (P i) ∧
      (weightedEdgeCost (graph A) (weights c) (weights (solutionWeights x)) : ℝ)≤(budget : ℝ) := by
  let input := rows A c P (target : ℚ) budget
  have xNonnegative := ((satisfies_iff A c P (target : ℚ) budget x).mp rational).nonnegative
  let y : Fin (dimension n m) → ℝ := fun j => x j
  have real := RationalFourierMotzkin.rational_to_real input x rational
  have fields := (satisfies_iff A c P (target : ℚ) budget y).mp real
  let w := weights (solutionWeights x)
  let p (i : Fin m) (v : Fin n) : ℝ≥0 := ⟨potentialValues y i v,fields.nonnegative (potentialIndex i v)⟩
  have fit : SparsestNormalizedPotentials.Feasible (graph A) w P (target : ℝ≥0) p := by
    refine ⟨?_,?_,?_⟩
    · intro i
      apply NNReal.eq
      exact le_antisymm (fields.origin i) (p i (P i).1).coe_nonneg
    · intro i u v edge
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_add,weight_readback x xNonnegative (u,v)]
      exact fields.step i (u,v) edge
    · apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_sum]
      exact fields.normalize
  have finite (i : Fin m) : edgeDistance (graph A) w (P i).1 (P i).2≠⊤ :=
    fun h => ((edgeDistance_eq_top_iff (graph A) w (P i).1 (P i).2).mp h) (reachable i)
  have within := fields.affordable
  rw [price_sum A c w y (fun e => (weight_readback x xNonnegative e).symm)] at within
  exact ⟨(SparsestNormalizedPotentials.normalization_iff (graph A) w P _ finite).mp ⟨p,fit⟩,within⟩

theorem findWeights_sound {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (budget : ℚ)
    (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2)) {w : Weights n}
    (found : findWeights A c P target budget=some w) :
    (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) (weights w) (P i) ∧
      (weightedEdgeCost (graph A) (weights c) (weights w) : ℝ)≤(budget : ℝ) := by
  obtain ⟨x,observed,rfl⟩ := Option.map_eq_some_iff.mp found
  exact assignment_sound A c P target budget reachable x (RationalFourierMotzkin.solve_sound _ x observed)

theorem findWeights_complete {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (budget : ℚ) (w : Fin n × Fin n → ℝ≥0)
    (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    (normalize : (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) w (P i))
    (affordable : (weightedEdgeCost (graph A) (weights c) w : ℝ)≤(budget : ℝ)) :
    (findWeights A c P target budget).isSome := by
  have finite (i : Fin m) : edgeDistance (graph A) w (P i).1 (P i).2≠⊤ :=
    fun h => ((edgeDistance_eq_top_iff (graph A) w (P i).1 (P i).2).mp h) (reachable i)
  obtain ⟨p,fit⟩ := (SparsestNormalizedPotentials.normalization_iff (graph A) w P _ finite).mpr normalize
  let x (j : Fin (dimension n m)) : ℝ :=
    ((coordinates n m).symm j).elim (fun e => (w e : ℝ)) (fun (i,v) => (p i v : ℝ))
  have row (e : Fin n × Fin n) : weightValues x e=(w e : ℝ) := by
    simp only [weightValues,x,weightIndex,Equiv.symm_apply_apply,Sum.elim_inl]
  have potential (i : Fin m) (v : Fin n) : potentialValues x i v=(p i v : ℝ) := by
    simp only [potentialValues,x,potentialIndex,Equiv.symm_apply_apply,Sum.elim_inr]
  have all : Constraints A c P (target : ℚ) budget x := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j
      unfold x
      cases (coordinates n m).symm j with
      | inl e => exact (w e).coe_nonneg
      | inr i => exact (p i.1 i.2).coe_nonneg
    · intro i
      rw [potential,fit.start i,NNReal.coe_zero]
    · intro i e edge
      rw [potential,potential,row]
      exact_mod_cast fit.arc i e.1 e.2 edge
    · simp only [potential]
      exact_mod_cast fit.total
    · rw [price_sum A c w x row]
      exact affordable
  unfold findWeights solve
  rw [Option.isSome_map]
  exact RationalFourierMotzkin.solve_complete _ x ((satisfies_iff ..).mpr all)

private def appendCoordinate {k : ℕ} (coefficient : ℚ) (r : Row k) : Row (k+1) :=
  ⟨Fin.lastCases coefficient r.coeff,r.constant⟩

private theorem append_eval {k : ℕ} (coefficient : ℚ) (r : Row k) (x : Fin (k+1) → ℚ) :
    (appendCoordinate coefficient r).eval x =
      r.eval (fun j => x j.castSucc)+coefficient*x (Fin.last k) := by
  simp only [appendCoordinate,Row.eval,Rat.cast_id,Fin.sum_univ_castSucc,Fin.lastCases_castSucc,Fin.lastCases_last]
  ring

private def fixed {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n) (target : ℚ) :
    List (Row (dimension n m)) :=
  (rows A c P target 0).dropLast

private theorem rows_split {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target budget : ℚ) :
    rows A c P target budget=fixed A c P target++[price n m A c budget] := by
  simp [fixed,rows,List.append_assoc]

def objectiveRows {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n) (target : ℚ) :
    List (Row (dimension n m+1)) :=
  (fixed A c P target).map (appendCoordinate 0)++[appendCoordinate 1 (price n m A c 0)]

theorem objectiveRows_spec {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ) (x : Fin (dimension n m+1) → ℚ) :
    Satisfies (objectiveRows A c P target) x ↔
      Satisfies (rows A c P target (x (Fin.last (dimension n m)))) (fun j => x j.castSucc) := by
  let q := x (Fin.last (dimension n m))
  let y : Fin (dimension n m) → ℚ := fun j => x j.castSucc
  have fee : (appendCoordinate 1 (price n m A c 0)).eval x=(price n m A c q).eval y := by
    simp only [append_eval,price_eval,Rat.cast_id,one_mul,zero_sub,q,y]
    ring
  constructor
  · intro yes r present
    rw [rows_split] at present
    rcases List.mem_append.mp present with others | atPrice
    · have lifted := yes (appendCoordinate 0 r)
        (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨r,others,rfl⟩)))
      simpa only [append_eval,zero_mul,add_zero] using lifted
    · rw [List.mem_singleton] at atPrice
      subst r
      rw [←fee]
      exact yes _ (List.mem_append.mpr (.inr List.mem_cons_self))
  · intro yes r present
    have before := rows_split A c P target q
    rcases List.mem_append.mp present with others | atPrice
    · obtain ⟨old,h,rfl⟩ := List.mem_map.mp others
      have observed := yes old (by rw [before]; exact List.mem_append.mpr (.inl h))
      simpa only [append_eval,zero_mul,add_zero] using observed
    · rw [List.mem_singleton] at atPrice
      subst r
      rw [fee]
      exact yes _ (by rw [before]; exact List.mem_append.mpr (.inr List.mem_cons_self))

def minimize {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) : Option (ℚ × Weights n) :=
  (RationalFourierMotzkin.minimizeLast (dimension n m) (objectiveRows A c P (target : ℚ))).map
    fun (q,x) => (q,solutionWeights fun j => x j.castSucc)

private theorem comparison_assignment {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (P : Fin m → Fin n × Fin n) (target : ℚ≥0) (budget : ℚ)
    (w : Fin n × Fin n → ℝ≥0)
    (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    (normalized : (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) w (P i))
    (within : (weightedEdgeCost (graph A) (weights c) w : ℝ)≤(budget : ℝ)) :
    ∃ x : Fin (dimension n m+1) → ℚ, x (Fin.last (dimension n m))=budget ∧
      Satisfies (objectiveRows A c P (target : ℚ)) x := by
  have feasible := findWeights_complete A c P target budget w reachable normalized within
  unfold findWeights at feasible
  rw [Option.isSome_map] at feasible
  cases found : solve A c P target budget with
  | none => rw [found] at feasible; cases feasible
  | some y =>
    let x : Fin (dimension n m+1) → ℚ := Fin.snoc (α := fun _ => ℚ) y budget
    refine ⟨x,Fin.snoc_last _ _,?_⟩
    apply (objectiveRows_spec A c P (target : ℚ) x).mpr
    have fit := RationalFourierMotzkin.solve_sound _ y found
    simpa only [x,Fin.snoc_last,Fin.snoc_castSucc] using fit

theorem minimize_complete {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (w : Fin n × Fin n → ℝ≥0)
    (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    (normalized : (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) w (P i)) :
    (minimize A c P target).isSome := by
  let budget : ℚ := ⌈(weightedEdgeCost (graph A) (weights c) w : ℝ)⌉₊
  have fit : (weightedEdgeCost (graph A) (weights c) w : ℝ)≤(budget : ℝ) := by
    simpa only [budget,Rat.cast_natCast] using Nat.le_ceil (weightedEdgeCost (graph A) (weights c) w : ℝ)
  obtain ⟨x,last,valid⟩ := comparison_assignment A c P target budget w reachable normalized fit
  have nonnegative : 0≤x (Fin.last (dimension n m)) := by rw [last]; positivity
  unfold minimize
  rw [Option.isSome_map]
  exact RationalFourierMotzkin.minimizeLast_complete _ _ x nonnegative valid

theorem minimize_attained {m n : ℕ} (A : Adjacency n) (c : Weights n) (P : Fin m → Fin n × Fin n)
    (target : ℚ≥0) (reachable : ∀ i, Nonempty (SimplePath (graph A) (P i).1 (P i).2))
    {q : ℚ} {w : Weights n} (returned : minimize A c P target=some (q,w)) :
    (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) (weights w) (P i) ∧
      (weightedEdgeCost (graph A) (weights c) (weights w) : ℝ)=(q : ℝ) ∧
      ∀ other : Fin n × Fin n → ℝ≥0,
        (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) other (P i) →
          (q : ℝ)≤(weightedEdgeCost (graph A) (weights c) other : ℝ) := by
  obtain ⟨answer,solved,returned⟩ := Option.map_eq_some_iff.mp returned
  obtain ⟨best,x⟩ := answer
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj returned
  obtain ⟨_,last,valid⟩ := RationalFourierMotzkin.minimizeLast_sound _ _ solved
  have assigned := (objectiveRows_spec A c P (target : ℚ) x).mp valid
  rw [last] at assigned
  obtain ⟨normalize,paid⟩ := assignment_sound A c P target best reachable _ assigned
  have least (other : Fin n × Fin n → ℝ≥0)
      (good : (target : ℝ≥0)≤∑ i, SparsestEdgeBridge.demandDistance (graph A) other (P i)) :
      (best : ℝ)≤(weightedEdgeCost (graph A) (weights c) other : ℝ) := by
    by_contra h
    obtain ⟨b,above,below⟩ := exists_rat_btwn (lt_of_not_ge h)
    obtain ⟨y,quantity,feasible⟩ :=
      comparison_assignment A c P target b other reachable good above.le
    have nonnegative : 0≤y (Fin.last (dimension n m)) := by
      rw [quantity]
      exact_mod_cast (NNReal.coe_nonneg (weightedEdgeCost (graph A) (weights c) other)).trans above.le
    have comparison := RationalFourierMotzkin.minimizeLast_optimal _ _ solved y nonnegative feasible
    rw [quantity] at comparison
    exact (not_lt_of_ge (by exact_mod_cast comparison : (best : ℝ)≤(b : ℝ))) below
  exact ⟨normalize,le_antisymm paid (least _ normalize),least⟩

end DirectedFlowCutGap.NormalizedEdgeLP
