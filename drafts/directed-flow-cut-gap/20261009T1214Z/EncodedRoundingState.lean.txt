import DirectedFlowCutGap.EncodedRoundingInput
import DirectedFlowCutGap.RetainedCandidateSolver

/-!
# Counted retained family, mass, and state operations

The candidate dictionary is supplied once and retained. Each active label calls
the concrete early-stop solver once and retains its entire array row. No mass
scan calls the optimizer. All finite index scans and array copies have explicit
charges, including zero rows for inactive labels. The functional refinement is
equality with the exact provider at this same generated enumeration.
-/
namespace DirectedFlowCutGap.EncodedRoundingState
open scoped BigOperators NNReal
open RetainedGridState EncodedRoundingInput EncodedIntegerShortestPaths
open FlexibleGridProvider FlexibleCandidateSchedule

/-- A counted finite sum, whose callback and materialization costs are retained. -/
def sumTabulate {m : ℕ} (f : Fin m → ℕ × ℕ) : ℕ × ℕ :=
  let r := tabulate f
  (r.1.toList.sum,r.2+4*m+2)

def sumOverhead (m : ℕ) : ℕ := arrayBound m+4*m+2

theorem sumTabulate_value {m : ℕ} (f : Fin m → ℕ × ℕ) :
    (sumTabulate f).1 = ∑ i : Fin m, (f i).1 := by
  simp only [sumTabulate,tabulate_value,Vector.toList_ofFn,List.sum_ofFn]

theorem sumTabulate_bound {m : ℕ} (f : Fin m → ℕ × ℕ) (C : ℕ)
    (h : ∀ i, (f i).2 ≤ C) : (sumTabulate f).2 ≤ m*C+sumOverhead m := by
  have hh := tabulate_bound f C h
  simp only [sumTabulate,sumOverhead]
  omega

variable {n L : ℕ}

/-- The inner sum scans retained array coordinates only. -/
def mass (a : PairFlags n) (x : Flags n) (w : Family n) : ℕ × ℕ :=
  sumTabulate fun u : Fin n => sumTabulate fun v : Fin n =>
    if flag a (u,v) then
      let r := sumTabulate fun z : Fin n => (if x[z.val] then 0 else (row w (u,v))[z.val],7)
      (r.1,r.2+4)
    else (0,4)

def massBound (n : ℕ) : ℕ :=
  n*(n*(n*7+sumOverhead n+4)+sumOverhead n)+sumOverhead n

theorem mass_value (a : PairFlags n) (x : Flags n) (w : Family n) :
    (mass a x w).1 = massNumerator a x w := by
  simp only [mass,sumTabulate_value,massNumerator,remainingSet,Finset.sum_filter,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  cases ha : flag a (u,v) <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  apply Finset.sum_congr rfl
  intro z _
  cases hx : x[z.val] <;> simp

theorem mass_bound (a : PairFlags n) (x : Flags n) (w : Family n) :
    (mass a x w).2 ≤ massBound n := by
  apply sumTabulate_bound
  intro u
  apply sumTabulate_bound
  intro v
  split
  · have h := sumTabulate_bound (fun z : Fin n =>
        (if x[z.val] then 0 else (row w (u,v))[z.val],7)) 7 (by intro z; rfl)
    dsimp only
    omega
  · dsimp only
    omega

def erase (a : PairFlags n) (p : Pair n) : PairFlags n × ℕ :=
  tabulate fun s : Fin n => tabulate fun t : Fin n =>
    (if (s,t)=p then false else flag a (s,t),8)

def union (x y : Flags n) : Flags n × ℕ :=
  tabulate fun v : Fin n => (x[v.val] || y[v.val],5)

def eraseBound (n : ℕ) : ℕ := n*(8*n+arrayBound n)+arrayBound n
def unionBound (n : ℕ) : ℕ := 5*n+arrayBound n

theorem erase_value (a : PairFlags n) (p : Pair n) : (erase a p).1 = eraseFlag a p := by
  simp only [erase,tabulate_value,eraseFlag]

theorem union_value (x y : Flags n) : (union x y).1 = unionFlags x y := by
  simp only [union,tabulate_value,unionFlags]

theorem erase_bound (a : PairFlags n) (p : Pair n) : (erase a p).2 ≤ eraseBound n := by
  apply tabulate_bound
  intro s
  simpa only [Nat.mul_comm] using tabulate_bound (fun t : Fin n =>
    (if (s,t)=p then false else flag a (s,t),8)) 8 (by intro t; rfl)

theorem union_bound (x y : Flags n) : (union x y).2 ≤ unionBound n := by
  simpa only [union,unionBound,Nat.mul_comm] using tabulate_bound
    (fun v : Fin n => (x[v.val] || y[v.val],5)) 5 (by intro v; rfl)

def roundData (s : Data n) (p : Pair n) (y : Flags n) : Data n × ℕ :=
  let a := erase s.remaining p
  let x := union s.cut y
  let m := mass a.1 x.1 s.weights
  ({s with remaining := a.1,cut := x.1,current := m.1},a.2+x.2+m.2+8)

theorem roundData_value (s : Data n) (p : Pair n) (y : Flags n) :
    (roundData s p y).1 = s.round p y := by
  simp only [roundData,erase_value,union_value,mass_value,Data.round]

theorem roundData_bound (s : Data n) (p : Pair n) (y : Flags n) :
    (roundData s p y).2 ≤ eraseBound n+unionBound n+massBound n+8 := by
  have ha := erase_bound s.remaining p
  have hx := union_bound s.cut y
  have hm := mass_bound (erase s.remaining p).1 (union s.cut y).1 s.weights
  dsimp only [roundData]
  omega

section Adapter
variable (adjacency : PairFlags n) (F : CandidateEnumeration.Factory n L)
variable (horder : F.base.enumeration.vertices = List.finRange n) (hL : 0<L)
variable {demands : Finset (Pair n)}

abbrev Witness := providerWitness (provider
  (FlexibleClosureRounding.closureGridOptimizer (G := graph adjacency) (D := demands)
    hL F.network.enumeration))

/-- The only candidate calls in the family builder occur in its true branch. -/
def family (s : Code (graph adjacency) demands L) : Family n × ℕ :=
  tabulate fun u : Fin n => tabulate fun v : Fin n =>
    if flag s.data.remaining (u,v) then
      let r := RetainedCandidateSolver.arrayRow F
        (RetainedCandidateSolver.input adjacency s.data.cut) u v (4*s.data.scale)
      (r.1,r.2+5)
    else (Vector.replicate n 0,2*n+5)

def candidateBound (n L : ℕ) : ℕ := EncodedCandidateOutput.operationBound n L+n^2+7*n+3
/-- This overhead includes every inactive row, even though active rows have
already been charged by the candidate solver. It deliberately overcounts. -/
def familyOverhead (n : ℕ) : ℕ := n*n*(2*n+5)+(n+1)*arrayBound n

theorem family_value (s : Code (graph adjacency) demands L) :
    (family adjacency F s).1 = buildFamily (RetainedCandidateSolver.optimizer adjacency F horder hL) s := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [family,tabulate_value,buildFamily,Vector.getElem_ofFn,
    RetainedCandidateSolver.optimizer,RetainedCandidateSolver.row]
  split <;> rfl

theorem active_sum (a : PairFlags n) (C : ℕ) :
    (∑ u : Fin n, ∑ v : Fin n, if flag a (u,v) then C else 0) = (remainingSet a).card*C := by
  have h := Fintype.sum_prod_type (fun p : Pair n => if flag a p then C else 0)
  rw [← h]
  simp [remainingSet,← Finset.sum_filter]

theorem family_bound (s : Code (graph adjacency) demands L) :
    (family adjacency F s).2 ≤
      (remainingSet s.data.remaining).card*candidateBound n L+familyOverhead n := by
  have hpoint (u v : Fin n) :
      (if flag s.data.remaining (u,v) then
        let r := RetainedCandidateSolver.arrayRow F
          (RetainedCandidateSolver.input adjacency s.data.cut) u v (4*s.data.scale)
        (r.1,r.2+5)
      else (Vector.replicate n 0,2*n+5)).2 ≤
        (if flag s.data.remaining (u,v) then candidateBound n L else 0)+(2*n+5) := by
    cases hp : flag s.data.remaining (u,v)
    · simp
    · have hr := RetainedCandidateSolver.arrayRow_bound F
        (RetainedCandidateSolver.input adjacency s.data.cut) u v (4*s.data.scale)
      simp only [ite_true]
      unfold candidateBound
      omega
  simp only [family,tabulate_work]
  calc
    (∑ u : Fin n, ((∑ v : Fin n, _)+arrayBound n))+arrayBound n ≤
        (∑ u : Fin n, ((∑ v : Fin n,
          ((if flag s.data.remaining (u,v) then candidateBound n L else 0)+(2*n+5)))+
          arrayBound n))+arrayBound n := by
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro u hu
      apply Nat.add_le_add_right
      apply Finset.sum_le_sum
      intro v hv
      exact hpoint u v
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        smul_eq_mul,active_sum]
      unfold familyOverhead
      ring

/-- A counted refresh stores the computed family and its computed mass once. -/
def refresh (s : Code (graph adjacency) demands L) : Cache (Witness (demands := demands) adjacency F hL) × ℕ :=
  let w := family adjacency F s
  let m := mass s.data.remaining s.data.cut w.1
  ({state := s,candidate := w.1,optimal := m.1,
    candidate_eq := by rw [family_value adjacency F horder hL]; exact buildFamily_eq _ s,
    optimal_eq := mass_value _ _ _},w.2+m.2+4)

theorem refresh_value (s : Code (graph adjacency) demands L) :
    (refresh adjacency F horder hL s).1 =
      RetainedGridState.refresh (RetainedCandidateSolver.optimizer adjacency F horder hL) s := by
  simp only [refresh,family_value adjacency F horder hL s,mass_value,RetainedGridState.refresh]
  rfl

theorem refresh_bound (s : Code (graph adjacency) demands L) :
    (refresh adjacency F horder hL s).2 ≤
      (remainingSet s.data.remaining).card*candidateBound n L+
        familyOverhead n+massBound n+4 := by
  have hf := family_bound adjacency F s
  have hm := mass_bound s.data.remaining s.data.cut (family adjacency F s).1
  dsimp only [refresh]
  omega

/-- A round changes the mask/cut and recomputes mass without changing weights. -/
def sampleRound (s : Code (graph adjacency) demands L) (p : Pair n)
    (hp : p ∈ (interpret s).remaining) (j : Fin L) : Code (graph adjacency) demands L × ℕ :=
  let y := cutFlags F.base.enumeration adjacency (row s.data.weights p) p.1 j.val
  let d := roundData s.data p y.1
  (⟨d.1,by
    rw [roundData_value]
    exact (RetainedGridState.sampleRound hL (cutOracle F.base.enumeration adjacency hL) s p hp j).valid⟩,
    y.2+d.2+3)

theorem sampleRound_value (s : Code (graph adjacency) demands L) (p : Pair n)
    (hp : p ∈ (interpret s).remaining) (j : Fin L) :
    (sampleRound adjacency F hL s p hp j).1 =
      RetainedGridState.sampleRound hL (cutOracle F.base.enumeration adjacency hL) s p hp j := by
  simp only [sampleRound,roundData_value,RetainedGridState.sampleRound,cutOracle]

def roundOverhead (n : ℕ) : ℕ := cutBound n+eraseBound n+unionBound n+11

theorem sampleRound_bound (s : Code (graph adjacency) demands L) (p : Pair n)
    (hp : p ∈ (interpret s).remaining) (j : Fin L) :
    (sampleRound adjacency F hL s p hp j).2 ≤ roundOverhead n+massBound n := by
  have hy := cutFlags_bound F.base.enumeration adjacency (row s.data.weights p) p.1 j.val
  have hd := roundData_bound s.data p
    (cutFlags F.base.enumeration adjacency (row s.data.weights p) p.1 j.val).1
  dsimp only [sampleRound]
  unfold roundOverhead
  omega

end Adapter
end DirectedFlowCutGap.EncodedRoundingState
