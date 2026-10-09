import DirectedFlowCutGap.CandidateEnumeration
import DirectedFlowCutGap.EncodedCandidateOutput
import DirectedFlowCutGap.EarlyStopRetainedFlow
import DirectedFlowCutGap.RetainedGridState

/-!
# Concrete retained candidate solver and adaptive optimizer adapter

The entry constructs the finite input once. The backend receives the dictionary
wrapping the retained network enumeration. One capacity table, one budget and
one early-stopping retained-edge flow invocation produce one numerator list. Its list order
and values are exactly those of the frozen finiteHooks provider at the generated
E. No runtime bound is attributed to the older ClosureRuntime implementation.

The Optimizer below retains this numerator list before materializing its row.
Array construction traverses that list once and explicitly charges all append
copying. The candidate and row bounds include this final materialization in
the same declared word model; allocator/compiler behavior remains separate.
-/
set_option synthInstance.maxSize 4096

namespace DirectedFlowCutGap.RetainedCandidateSolver

open scoped BigOperators NNReal
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open CandidateGridOptimizer CandidateThresholdClosure CandidatePortDifferenceSystem
open CandidateClosureProvider MinimumClosureCut MinimumClosureOptimizer
open EncodedCandidateCapacity EncodedCandidateOutput

variable {n L : ℕ}

/-- The executable generic backend receives the already built dictionary.
Canonical-dictionary equality appears only in the erased refinement proofs. -/
def backend (F : CandidateEnumeration.Factory n L)
    (cs : List ((CandidateEnumeration.Network n L × CandidateEnumeration.Network n L) × ℤ))
    (k : ℕ) : CountedFlow.CutOutput (CandidateEnumeration.Network n L) :=
  @EarlyStopRetainedFlow.solve (CandidateEnumeration.Network n L) F.network.dictionary
    inferInstance cs F.network.enumeration source sink k

theorem backend_vertices (F : CandidateEnumeration.Factory n L)
    (cs : List ((CandidateEnumeration.Network n L × CandidateEnumeration.Network n L) × ℤ))
    (k : ℕ) :
    (backend F cs k).vertices =
      (CountedFlow.solve cs F.network.enumeration source sink k).vertices := by
  have h : F.network.dictionary = (inferInstance : Fintype (CandidateEnumeration.Network n L)) :=
    Subsingleton.elim _ _
  unfold backend
  rw [h]
  exact (EarlyStopRetainedFlow.solve_vertices cs F.network.enumeration source sink k).trans
    (RetainedPathFlow.solve_vertices cs F.network.enumeration source sink k)

theorem backend_bound (F : CandidateEnumeration.Factory n L)
    (cs : List ((CandidateEnumeration.Network n L × CandidateEnumeration.Network n L) × ℤ))
    (k : ℕ) (hc : cs.length = (Fintype.card (CandidateEnumeration.Network n L))^2) :
    (backend F cs k).work ≤ 256*(k+1)*(6*n*(L+1)+3)^5 := by
  have h : F.network.dictionary = (inferInstance : Fintype (CandidateEnumeration.Network n L)) :=
    Subsingleton.elim _ _
  unfold backend
  rw [h]
  simpa only [Input.network_card] using
    EarlyStopRetainedFlow.solve_word_polynomial cs F.network.enumeration source sink k hc

/-- Each stage closes only over already retained output from its predecessor. -/
def solveWith (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) : Output n :=
  let c := D.construct s t L B F.nodes.enumeration F.network.enumeration
  let f := backend F c.cells c.budget
  let r := coreScan f.vertices
  let out := numeratorScan D L r.1 F.base.enumeration.vertices
  ⟨out.1,c.work+f.work+r.2+out.2+4⟩

/-- Ordered equality uses the same E, not uniqueness of an optimum. -/
theorem solveWith_numerators (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) :
    (solveWith F D s t B).numerators =
      (EncodedCandidateOutput.solve D s t L B F.nodes.enumeration
        F.network.enumeration F.base.enumeration).numerators := by
  simp only [solveWith,EncodedCandidateOutput.solve,backend_vertices]

theorem solveWith_finiteHooks (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) (hL : 0<L)
    (hf : CandidateFeasible D.graph s t D.cut L B) :
    (solveWith F D s t B).numerators = F.base.enumeration.vertices.map fun v =>
      (v,candidateNumerator D.graph s t D.cut L B hL
        (finiteHooks (candidateClosure D.graph s t D.cut L B) F.network.enumeration) hf v) := by
  rw [solveWith_numerators]
  exact EncodedCandidateOutput.solve_finiteHooks D s t L B hL
    F.nodes.enumeration F.network.enumeration F.base.enumeration hf

theorem solveWith_length (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) : (solveWith F D s t B).numerators.length = n := by
  rw [solveWith_numerators]
  exact EncodedCandidateOutput.solve_length D s t L B
    F.nodes.enumeration F.network.enumeration F.base.enumeration

theorem solveWith_bound (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) :
    (solveWith F D s t B).work ≤ EncodedCandidateOutput.operationBound n L := by
  let c := D.construct s t L B F.nodes.enumeration F.network.enumeration
  let f := backend F c.cells c.budget
  have hc := D.construct_bound s t L B F.nodes.enumeration F.network.enumeration
  have hf := backend_bound F c.cells c.budget
    (D.construct_length s t L B F.nodes.enumeration F.network.enumeration)
  have hb := candidate_budget_le D.graph s t D.cut L B
  simp only [Fintype.card_fin] at hb
  have hcb : c.budget ≤ 6*n*(L+1) := by simpa [c] using hb
  have hfl : f.vertices.length ≤ 6*n*(L+1)+2 := by
    have h := List.Nodup.length_le_card f.nodup
    rw [Input.network_card] at h
    exact h
  have hcore := coreScan_bound f.vertices
  have hcorelen := (coreScan_length f.vertices).trans hfl
  have hout := numeratorScan_bound D L (coreScan f.vertices).1 F.base.enumeration.vertices
  rw [F.base.enumeration.length_eq_card,Fintype.card_fin] at hout
  have hf' := hf.trans (Nat.mul_le_mul_right ((6*n*(L+1)+3)^5)
    (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hcb 1)))
  have hout' := hout.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 28 hcorelen) 12)) 1)
  have hcore' := hcore.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hfl) 1)
  change c.work ≤ 90*(6*n*(L+1)+3)^2 at hc
  change f.work ≤ 256*(6*n*(L+1)+1)*(6*n*(L+1)+3)^5 at hf'
  change c.work+f.work+(coreScan f.vertices).2+
    (numeratorScan D L (coreScan f.vertices).1 F.base.enumeration.vertices).2+4 ≤
    90*(6*n*(L+1)+3)^2+256*(6*n*(L+1)+1)*(6*n*(L+1)+3)^5+
      4*(6*n*(L+1)+2)+1+n*(28*(6*n*(L+1)+2)+12)+1+4
  omega

/-- Complete candidate entry. A surrounding hard/easy dispatcher must check
L≤n before this call, so a huge binary threshold never allocates its levels. -/
def solve (D : Input n) (s t : Fin n) (L B : ℕ) : Output n :=
  let F := CandidateEnumeration.make n L
  let r := solveWith F D s t B
  ⟨r.numerators,F.work+r.work+2⟩

def operationBound (n L : ℕ) : ℕ :=
  60*(6*n*(L+1)+3)+EncodedCandidateOutput.operationBound n L+2

theorem solve_bound (D : Input n) (s t : Fin n) (L B : ℕ) :
    (solve D s t L B).work ≤ operationBound n L := by
  have hn : 0<n := by have h := s.isLt; omega
  have hf := CandidateEnumeration.make_network_bound n L hn
  have hs := solveWith_bound (CandidateEnumeration.make n L) D s t B
  change (CandidateEnumeration.make n L).work+
    (solveWith (CandidateEnumeration.make n L) D s t B).work+2 ≤ _
  unfold operationBound
  omega

/-- The guarded candidate branch is polynomial in vertex count. The binary
epoch cap B changes operand width, never a loop bound in this program. -/
theorem solve_polynomial (D : Input n) (s t : Fin n) (L B : ℕ) (hL : L≤n) :
    (solve D s t L B).work ≤ operationBound n n := by
  apply (solve_bound D s t L B).trans
  unfold operationBound EncodedCandidateOutput.operationBound
  dsimp only
  gcongr

theorem solve_finiteHooks (D : Input n) (s t : Fin n) (L B : ℕ) (hL : 0<L)
    (hf : CandidateFeasible D.graph s t D.cut L B) :
    (solve D s t L B).numerators = (List.finRange n).map fun v =>
      (v,candidateNumerator D.graph s t D.cut L B hL
        (finiteHooks (candidateClosure D.graph s t D.cut L B)
          (CandidateEnumeration.make n L).network.enumeration) hf v) := by
  change (solveWith (CandidateEnumeration.make n L) D s t B).numerators = _
  rw [solveWith_finiteHooks _ D s t B hL hf]
  rw [show (CandidateEnumeration.make n L).base.enumeration.vertices = List.finRange n from
    CandidateEnumeration.fin_vertices n]

theorem solve_numerator_bits (D : Input n) (s t : Fin n) (L B : ℕ) (hL : 0<L)
    (hf : CandidateFeasible D.graph s t D.cut L B) (v : Fin n) (z : ℤ)
    (hz : (v,z) ∈ (solve D s t L B).numerators) :
    1+Nat.size z.natAbs ≤ 1+Nat.size L := by
  change (v,z) ∈ (solveWith (CandidateEnumeration.make n L) D s t B).numerators at hz
  rw [solveWith_numerators] at hz
  exact EncodedCandidateOutput.solve_numerator_bits D s t L B hL _ _ _ hf v z hz

/-- Materialize the retained numerators in their existing order. Every suffix
copy is charged, so no amortized constant-time array-growth premise is needed. -/
def scalarArray : List (Fin n × ℤ) → Array ℕ × ℕ
  | [] => (#[],1)
  | e::es =>
    let r := scalarArray es
    (#[e.2.toNat]++r.1,r.2+2*r.1.size+8)

theorem scalarArray_value (xs : List (Fin n × ℤ)) :
    (scalarArray xs).1.toList = xs.map fun e => e.2.toNat := by
  induction xs <;> simp [scalarArray, *]

theorem scalarArray_size (xs : List (Fin n × ℤ)) : (scalarArray xs).1.size = xs.length := by
  have h := congrArg List.length (scalarArray_value xs)
  simpa using h

theorem scalarArray_work (xs : List (Fin n × ℤ)) :
    (scalarArray xs).2 = xs.length^2+7*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp only [scalarArray,scalarArray_size,List.length_cons,ih]; ring

/-- Vector proof fields are erased; the returned array is used directly. -/
def arrayRow (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) : RetainedGridState.Row n × ℕ :=
  let r := solveWith F D s t B
  let a := scalarArray r.numerators
  (⟨a.1,by rw [scalarArray_size,solveWith_length]⟩,r.work+a.2+2)

theorem arrayRow_list (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) :
    (arrayRow F D s t B).1.toList =
      (solveWith F D s t B).numerators.map fun e => e.2.toNat :=
  scalarArray_value _

theorem arrayRow_bound (F : CandidateEnumeration.Factory n L) (D : Input n)
    (s t : Fin n) (B : ℕ) :
    (arrayRow F D s t B).2 ≤ EncodedCandidateOutput.operationBound n L+n^2+7*n+3 := by
  have h := solveWith_bound F D s t B
  simp only [arrayRow,scalarArray_work,solveWith_length]
  omega

/-- One-call version that includes both factory preparation and natural-array
materialization in its returned charge. -/
def solveRow (D : Input n) (s t : Fin n) (L B : ℕ) : RetainedGridState.Row n × ℕ :=
  let F := CandidateEnumeration.make n L
  let r := arrayRow F D s t B
  (r.1,F.work+r.2+2)

theorem solveRow_bound (D : Input n) (s t : Fin n) (L B : ℕ) :
    (solveRow D s t L B).2 ≤ operationBound n L+n^2+7*n+3 := by
  have hn : 0<n := by have h := s.isLt; omega
  have hf := CandidateEnumeration.make_network_bound n L hn
  have hr := arrayRow_bound (CandidateEnumeration.make n L) D s t B
  unfold solveRow operationBound
  dsimp only
  omega

section Adapter
open RetainedGridState FlexibleGridProvider FlexibleCandidateSchedule CandidateOptimization

/-- The input graph is a retained Boolean matrix. -/
def graph (adjacency : PairFlags n) : Digraph (Fin n) where
  Adj u v := (adjacency[u.val])[v.val] = true

instance (adjacency : PairFlags n) : DecidableRel (graph adjacency).Adj := fun u v =>
  inferInstanceAs (Decidable ((adjacency[u.val])[v.val] = true))

def input (adjacency : PairFlags n) (removed : Flags n) : Input n := ⟨adjacency,removed⟩

@[simp] theorem input_graph (adjacency : PairFlags n) (removed : Flags n) :
    (input adjacency removed).graph = graph adjacency := rfl

@[simp] theorem input_cut (adjacency : PairFlags n) (removed : Flags n) :
    (input adjacency removed).cut = cutSet removed := rfl

variable {demands : Finset (Pair n)}

/-- The factory is retained by the optimizer, and each solve retains its whole
numerator list before materializing the natural array. -/
def row (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
    (s : Code (graph adjacency) demands L) (p : Pair n) : Row n :=
  (arrayRow F (input adjacency s.data.cut) p.1 p.2 (4*s.data.scale)).1

theorem row_eq (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
    (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0<L)
    (s : Code (graph adjacency) demands L) (p : Pair n) (hp : p ∈ (interpret s).remaining) :
    row adjacency F s p = RetainedGridState.closureRow hL F.network.enumeration s p hp := by
  let f := candidateNumerator (graph adjacency) p.1 p.2 (cutSet s.data.cut) L
    (4*s.data.scale) hL
    (finiteHooks (candidateClosure (graph adjacency) p.1 p.2 (cutSet s.data.cut) L
      (4*s.data.scale)) F.network.enumeration)
    (RetainedGridState.current_feasible_data s p hp)
  have hv : row adjacency F s p = Vector.ofFn (fun v => (f v).toNat) := by
    apply Vector.toList_inj.mp
    rw [show (row adjacency F s p).toList = _ from arrayRow_list F
      (input adjacency s.data.cut) p.1 p.2 (4*s.data.scale)]
    rw [solveWith_finiteHooks F (input adjacency s.data.cut) p.1 p.2 (4*s.data.scale) hL
      (RetainedGridState.current_feasible_data s p hp)]
    simp only [horder,List.map_map,Vector.toList_ofFn,List.ofFn_eq_map]
    rfl
  rw [hv]
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn]
  exact (RetainedGridState.closureRow_eq_numerator hL F.network.enumeration s p hp ⟨i,hi⟩).symm

/-- Exact adapter to the provider used in the separately proved execution law.
Its E is the factory's E throughout, so tie-breaking is preserved. -/
def optimizer (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
    (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0<L) :
    Optimizer (providerWitness (provider
      (FlexibleClosureRounding.closureGridOptimizer hL F.network.enumeration) :
        FamilyProvider (graph adjacency) demands (L : ℝ≥0))) where
  solve := fun s p _ => row adjacency F s p
  solve_eq := by
    intro s p hp v
    rw [row_eq adjacency F horder hL s p hp]
    exact (RetainedGridState.closureOptimizer hL F.network.enumeration).solve_eq s p hp v
  inactive_eq := (RetainedGridState.closureOptimizer hL F.network.enumeration).inactive_eq

private theorem optimizer_ext {G : Digraph (Fin n)} {D : Finset (Pair n)}
    {selector : FamilyProvider G D (L : ℝ≥0) → Prop} {H : ∃ P, selector P}
    (a b : Optimizer H) (h : a.solve = b.solve) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Extensional Optimizer equality is available to the retained law theorem;
the runtime claim belongs to this module's implementation and counter. -/
theorem optimizer_eq (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
    (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0<L) :
    optimizer (demands := demands) adjacency F horder hL =
      RetainedGridState.tabulatedOptimizer hL F.base.enumeration F.network.enumeration := by
  have hs : (optimizer (demands := demands) adjacency F horder hL).solve =
      (RetainedGridState.tabulatedOptimizer hL F.base.enumeration F.network.enumeration).solve := by
    funext s p hp
    rw [show (optimizer (demands := demands) adjacency F horder hL).solve s p hp = row adjacency F s p from rfl]
    rw [row_eq adjacency F horder hL s p hp]
    exact (RetainedGridState.tabulatedRow_eq hL F.base.enumeration F.network.enumeration s p hp).symm
  exact optimizer_ext _ _ hs

/-- Concrete input factory retained once in the returned optimizer closure. -/
def makeOptimizer (adjacency : PairFlags n) (L : ℕ) (hL : 0<L) :
    Optimizer (providerWitness (provider
      (FlexibleClosureRounding.closureGridOptimizer hL
        (CandidateEnumeration.make n L).network.enumeration) :
        FamilyProvider (graph adjacency) demands (L : ℝ≥0))) :=
  let F := CandidateEnumeration.make n L
  optimizer adjacency F (CandidateEnumeration.fin_vertices n) hL

theorem makeOptimizer_eq (adjacency : PairFlags n) (L : ℕ) (hL : 0<L) :
    makeOptimizer (demands := demands) adjacency L hL =
      RetainedGridState.tabulatedOptimizer hL
        (CandidateEnumeration.make n L).base.enumeration
        (CandidateEnumeration.make n L).network.enumeration :=
  optimizer_eq adjacency _ (CandidateEnumeration.fin_vertices n) hL

end Adapter
end DirectedFlowCutGap.RetainedCandidateSolver
