import DirectedFlowCutGap.EncodedCandidateCapacity
import DirectedFlowCutGap.CountedTabulatedFlow

/-!
# Counted retained candidate output

One encoded network construction and one tabulated flow solve produce a retained
cut. Core extraction and maximum-level decoding traverse retained lists only;
they cannot rerun the solver through a pointwise function. The output is one
list of integer numerators, extensionally identical to the frozen finite hooks.

The supplied enumerations are retained finite input data. The instruction model
is the concrete word model of `EncodedCandidateCapacity` and `CountedFlow`;
proofs and the ghost work annotations are excluded. This is not a certificate
for the implementation of Lean's allocator, GC, compiler or binary arithmetic.
-/
namespace DirectedFlowCutGap.EncodedCandidateOutput

open scoped BigOperators
open CandidateGridOptimizer CandidatePortDifferenceSystem CandidateThresholdClosure
open MinimumClosureProblem MinimumClosureCut MinimumClosureOptimizer IntegralNetworkFlow
open IntegralNetworkFlow.Tabulated EncodedCandidateCapacity CandidateClosureProvider

variable {A : Type*} [DecidableEq A]

/-- One pass through the retained cut, charging a list case, sum case, and
allocation/sequencing. No universe scan or duplicate removal is executed. -/
def coreScan : List (Vertex A) → List A × ℕ
  | [] => ([],1)
  | (.inl a)::xs => let r := coreScan xs; (a::r.1,r.2+4)
  | (.inr _)::xs => let r := coreScan xs; (r.1,r.2+3)

omit [DecidableEq A] in
@[simp] theorem coreScan_mem (a : A) (xs : List (Vertex A)) :
    a ∈ (coreScan xs).1 ↔ Sum.inl a ∈ xs := by
  induction xs with
  | nil => simp [coreScan]
  | cons x xs ih => cases x <;> simp [coreScan,ih]

omit [DecidableEq A] in
theorem coreScan_nodup (xs : List (Vertex A)) (h : xs.Nodup) :
    (coreScan xs).1.Nodup := by
  induction xs with
  | nil => simp [coreScan]
  | cons x xs ih =>
    have hh := List.nodup_cons.mp h
    cases x with
    | inl a =>
      change (a::(coreScan xs).1).Nodup
      refine List.nodup_cons.mpr ⟨?_,ih hh.2⟩
      simpa using hh.1
    | inr b => simpa [coreScan] using ih hh.2

omit [DecidableEq A] in
theorem coreScan_length (xs : List (Vertex A)) : (coreScan xs).1.length ≤ xs.length := by
  induction xs with
  | nil => simp [coreScan]
  | cons x xs ih => cases x <;> simp [coreScan] <;> omega

omit [DecidableEq A] in
theorem coreScan_bound (xs : List (Vertex A)) : (coreScan xs).2 ≤ 4*xs.length+1 := by
  induction xs with
  | nil => simp [coreScan]
  | cons x xs ih => cases x <;> simp only [coreScan,List.length_cons] <;> omega

variable [Fintype A]

theorem coreScan_set (r : CountedFlow.CutOutput (Vertex A)) :
    ClosureRuntime.setOfNodup (coreScan r.vertices).1 (coreScan_nodup _ r.nodup) =
      cores r.asSet := by
  ext a
  simp [MinimumClosureCut.core]

section Levels
variable {n L : ℕ}

/-- An initial zero and a complete retained-list maximum scan. Fourteen word
operations per cell cover the list case, fixed-arity point equality, branch,
maximum comparison/selection and allocation. -/
def maxLevel (i : Point (Fin n)) : List (Node (Point (Fin n)) L) → Fin (L+1) × ℕ
  | [] => (0,1)
  | a::as =>
    let r := maxLevel i as
    (if a.1=i then max a.2 r.1 else r.1,r.2+14)

theorem maxLevel_bound (i : Point (Fin n)) (xs : List (Node (Point (Fin n)) L)) :
    (maxLevel i xs).2 = 14*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [maxLevel,ih]; omega

theorem maxLevel_le_iff (i : Point (Fin n)) (xs : List (Node (Point (Fin n)) L))
    (k : Fin (L+1)) :
    (maxLevel i xs).1 ≤ k ↔ ∀ a ∈ xs, a.1=i → a.2≤k := by
  induction xs with
  | nil => simp [maxLevel]
  | cons a as ih =>
    by_cases h : a.1=i
    · simp [maxLevel,h,ih]
    · simp [maxLevel,h,ih]

/-- Equality with the existing nonempty-finset maximum, proved without using
that finset construction at runtime. -/
theorem maxLevel_decode
    (S : CandidateGridRounding.DifferenceSystem (Point (Fin n)) L)
    (c : Point (Fin n) → ℤ) (xs : List (Node (Point (Fin n)) L))
    (hn : xs.Nodup) (hc : (problem S c).IsClosed (ClosureRuntime.setOfNodup xs hn))
    (i : Point (Fin n)) :
    (maxLevel i xs).1 = decode S c (ClosureRuntime.setOfNodup xs hn) hc i := by
  apply le_antisymm
  · apply (maxLevel_le_iff i xs _).mpr
    intro a ha hi
    have hm : a.2 ∈ levels (ClosureRuntime.setOfNodup xs hn) i := by
      rw [mem_levels,← hi]
      simpa using ha
    exact Finset.le_max' _ _ hm
  · have hm : (i,decode S c (ClosureRuntime.setOfNodup xs hn) hc i) ∈ xs := by
      have h := Finset.max'_mem (levels (ClosureRuntime.setOfNodup xs hn) i)
        (levels_nonempty S c _ hc i)
      simpa [decode] using h
    exact (maxLevel_le_iff i xs (maxLevel i xs).1).mp le_rfl _ hm rfl

/-- The two maximum scans close only over `xs`. A removed vertex returns L
without either scan. Ten operations cover the list case, array read, branch,
casts/subtraction, key, list and result allocation, and sequencing. -/
def numeratorScan (D : Input n) (L : ℕ) (xs : List (Node (Point (Fin n)) L)) :
    List (Fin n) → List (Fin n × ℤ) × ℕ
  | [] => ([],1)
  | v::vs =>
    let r := numeratorScan D L xs vs
    if D.removed[v.val] then ((v,(L : ℤ))::r.1,r.2+6)
    else
      let a := maxLevel (TerminalPorts.core v,true) xs
      let b := maxLevel (TerminalPorts.core v,false) xs
      ((v,((a.1 : ℕ) : ℤ)-(b.1 : ℕ))::r.1,r.2+a.2+b.2+10)

theorem numeratorScan_value (D : Input n) (L : ℕ) (xs : List (Node (Point (Fin n)) L))
    (vs : List (Fin n)) :
    (numeratorScan D L xs vs).1 = vs.map fun v =>
      (v,if D.removed[v.val] then (L : ℤ) else
        (((maxLevel (TerminalPorts.core v,true) xs).1 : ℕ) : ℤ)-
          ((maxLevel (TerminalPorts.core v,false) xs).1 : ℕ)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => cases h : D.removed[v.val] <;> simp [numeratorScan,ih,h]

theorem numeratorScan_bound (D : Input n) (L : ℕ) (xs : List (Node (Point (Fin n)) L))
    (vs : List (Fin n)) :
    (numeratorScan D L xs vs).2 ≤ vs.length*(28*xs.length+12)+1 := by
  induction vs with
  | nil => simp [numeratorScan]
  | cons v vs ih =>
    have ha := maxLevel_bound (TerminalPorts.core v,true) xs
    have hb := maxLevel_bound (TerminalPorts.core v,false) xs
    simp only [numeratorScan,List.length_cons,Nat.add_mul,Nat.one_mul]
    split <;> dsimp only <;> omega

end Levels

structure Output (n : ℕ) where
  numerators : List (Fin n × ℤ)
  work : ℕ

variable {n : ℕ}

/-- A single construction, solver invocation, core pass and numerator pass. -/
def solve (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n)) : Output n :=
  let c := D.construct s t L B EN E
  let f := CountedFlow.solve c.cells E source sink c.budget
  let r := coreScan f.vertices
  let out := numeratorScan D L r.1 EV.vertices
  ⟨out.1,c.work+f.work+r.2+out.2+4⟩

theorem solved_cut_value (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) :
    (CountedFlow.solve (D.construct s t L B EN E).cells E source sink
      (D.construct s t L B EN E).budget).asSet =
    finiteResidualCut E (runFlow (candidateClosure D.graph s t D.cut L B)
      (finiteHooks (candidateClosure D.graph s t D.cut L B) E).search) := by
  have hc : CountedFlow.capacityOf (D.construct s t L B EN E).cells =
      capacity (candidateClosure D.graph s t D.cut L B) := D.construct_capacity s t L B EN E
  rw [CountedFlow.solve_value,hc,Input.construct_budget]
  rfl

theorem solved_cores_value (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L))) :
    let f := CountedFlow.solve (D.construct s t L B EN E).cells E source sink
      (D.construct s t L B EN E).budget
    ClosureRuntime.setOfNodup (coreScan f.vertices).1 (coreScan_nodup _ f.nodup) =
      (ClosureRuntime.solve (candidateClosure D.graph s t D.cut L B) E).1 := by
  dsimp only
  rw [coreScan_set,solved_cut_value,ClosureRuntime.solve_value]
  rfl

theorem solve_value (D : Input n) (s t : Fin n) (L B : ℕ) (hL : 0 < L)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n))
    (hfeas : CandidateFeasible D.graph s t D.cut L B) :
    (solve D s t L B EN E EV).numerators =
      ClosureRuntime.candidateNumerators D.graph s t D.cut L B hL EV E hfeas := by
  let f := CountedFlow.solve (D.construct s t L B EN E).cells E source sink
    (D.construct s t L B EN E).budget
  let xs := (coreScan f.vertices).1
  let hn := coreScan_nodup f.vertices f.nodup
  have he : ClosureRuntime.setOfNodup xs hn =
      (ClosureRuntime.solve (candidateClosure D.graph s t D.cut L B) E).1 :=
    solved_cores_value D s t L B EN E
  have hc := (ClosureRuntime.solve_optimal (candidateClosure D.graph s t D.cut L B) E
    (closure_nonempty (system D.graph s t D.cut L B) (integerCosts D.cut)
      (system_nonempty D.graph s t D.cut L B hL hfeas))).1
  have hcx : (problem (system D.graph s t D.cut L B) (integerCosts D.cut)).IsClosed
      (ClosureRuntime.setOfNodup xs hn) := by rw [he]; exact hc
  have hd (i : Point (Fin n)) := maxLevel_decode (system D.graph s t D.cut L B)
    (integerCosts D.cut) xs hn hcx i
  have hdecode (T U : Finset (Node (Point (Fin n)) L))
      (hT : (problem (system D.graph s t D.cut L B) (integerCosts D.cut)).IsClosed T)
      (hU : (problem (system D.graph s t D.cut L B) (integerCosts D.cut)).IsClosed U)
      (h : T = U) :
      decode (system D.graph s t D.cut L B) (integerCosts D.cut) T hT =
        decode (system D.graph s t D.cut L B) (integerCosts D.cut) U hU := by
    subst U
    rfl
  have hd' (i : Point (Fin n)) : (maxLevel i xs).1 =
      decode (system D.graph s t D.cut L B) (integerCosts D.cut)
        (ClosureRuntime.solve (candidateClosure D.graph s t D.cut L B) E).1 hc i :=
    (hd i).trans (congrFun (hdecode _ _ hcx hc he) i)
  change (numeratorScan D L xs EV.vertices).1 = _
  rw [numeratorScan_value]
  unfold ClosureRuntime.candidateNumerators
  dsimp only
  apply List.map_congr_left
  intro v _
  rw [hd',hd']
  cases h : D.removed[v.val] <;> simp [Input.mem_cut,h]

theorem solve_finiteHooks (D : Input n) (s t : Fin n) (L B : ℕ) (hL : 0 < L)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n))
    (hfeas : CandidateFeasible D.graph s t D.cut L B) :
    (solve D s t L B EN E EV).numerators = EV.vertices.map fun v =>
      (v,candidateNumerator D.graph s t D.cut L B hL
        (finiteHooks (candidateClosure D.graph s t D.cut L B) E) hfeas v) := by
  rw [solve_value D s t L B hL EN E EV hfeas,ClosureRuntime.candidateNumerators_value]

theorem solve_length (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n)) :
    (solve D s t L B EN E EV).numerators.length = n := by
  simp [solve,numeratorScan_value,EV.length_eq_card]

/-- For feasible inputs the actually retained numerator is nonnegative and
at most L, by identity with the exact deterministic candidate provider. -/
theorem solve_numerator_bounds (D : Input n) (s t : Fin n) (L B : ℕ) (hL : 0 < L)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n))
    (hfeas : CandidateFeasible D.graph s t D.cut L B) (v : Fin n) (z : ℤ)
    (hz : (v,z) ∈ (solve D s t L B EN E EV).numerators) : 0 ≤ z ∧ z ≤ L := by
  rw [solve_finiteHooks D s t L B hL EN E EV hfeas] at hz
  obtain ⟨u,_,h⟩ := List.mem_map.mp hz
  cases h
  exact ⟨candidateNumerator_nonneg D.graph s t D.cut L B hL _ hfeas v,
    candidateNumerator_le D.graph s t D.cut L B hL _ hfeas v⟩

theorem solve_numerator_bits (D : Input n) (s t : Fin n) (L B : ℕ) (hL : 0 < L)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n))
    (hfeas : CandidateFeasible D.graph s t D.cut L B) (v : Fin n) (z : ℤ)
    (hz : (v,z) ∈ (solve D s t L B EN E EV).numerators) :
    1+Nat.size z.natAbs ≤ 1+Nat.size L := by
  have h := solve_numerator_bounds D s t L B hL EN E EV hfeas v z hz
  have ha : z.natAbs ≤ L := by
    have hh := h.2
    rw [← Int.natAbs_of_nonneg h.1] at hh
    exact_mod_cast hh
  exact Nat.add_le_add_left (Nat.size_le_size ha) 1

/-- A polynomial that exposes each whole-program contribution. -/
def operationBound (n L : ℕ) : ℕ :=
  let N := 6*n*(L+1)+2
  90*(N+1)^2 + 256*(6*n*(L+1)+1)*(N+1)^5 + 4*N+1 + n*(28*N+12)+1+4

theorem solve_bound (D : Input n) (s t : Fin n) (L B : ℕ)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n)) :
    (solve D s t L B EN E EV).work ≤ operationBound n L := by
  let c := D.construct s t L B EN E
  let f := CountedFlow.solve c.cells E source sink c.budget
  have hc := D.construct_bound s t L B EN E
  have hf := CountedFlow.solve_word_polynomial c.cells E source sink c.budget
    (D.construct_length s t L B EN E)
  have hb := candidate_budget_le D.graph s t D.cut L B
  simp only [Fintype.card_fin] at hb
  have hcb : c.budget ≤ 6*n*(L+1) := by simpa [c] using hb
  have hfl : f.vertices.length ≤ 6*n*(L+1)+2 := by
    have h := List.Nodup.length_le_card f.nodup
    rw [Input.network_card] at h
    exact h
  have hcore := coreScan_bound f.vertices
  have hcorelen := (coreScan_length f.vertices).trans hfl
  have hout := numeratorScan_bound D L (coreScan f.vertices).1 EV.vertices
  rw [EV.length_eq_card,Fintype.card_fin] at hout
  rw [Input.network_card] at hf
  have hf' := hf.trans (Nat.mul_le_mul_right ((6*n*(L+1)+3)^5)
    (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hcb 1)))
  have hout' := hout.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 28 hcorelen) 12)) 1)
  have hcore' := hcore.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hfl) 1)
  change c.work ≤ 90*(6*n*(L+1)+3)^2 at hc
  change f.work ≤ 256*(6*n*(L+1)+1)*(6*n*(L+1)+3)^5 at hf'
  change c.work+f.work+(coreScan f.vertices).2+
    (numeratorScan D L (coreScan f.vertices).1 EV.vertices).2+4 ≤
    90*(6*n*(L+1)+3)^2+256*(6*n*(L+1)+1)*(6*n*(L+1)+3)^5+
      4*(6*n*(L+1)+2)+1+n*(28*(6*n*(L+1)+2)+12)+1+4
  omega

/-- With L at most n the displayed whole-program bound is a fixed polynomial
in n; no numerical dependence on the arbitrary epoch cap B occurs. -/
theorem solve_polynomial (D : Input n) (s t : Fin n) (L B : ℕ) (hL : L ≤ n)
    (EN : ResidualSearch.Enumeration (Node (Point (Fin n)) L))
    (E : ResidualSearch.Enumeration (Vertex (Node (Point (Fin n)) L)))
    (EV : ResidualSearch.Enumeration (Fin n)) :
    (solve D s t L B EN E EV).work ≤ operationBound n n := by
  apply (solve_bound D s t L B EN E EV).trans
  unfold operationBound
  dsimp only
  gcongr

end DirectedFlowCutGap.EncodedCandidateOutput
