import DirectedFlowCutGap.FrozenEpochProbability
import Mathlib.Data.List.OfFn

/-!
# An exact finite-input permutation sampler

The input tape contains independent uniform draws of bounds `n,n-1,...,1`.
The interpreter constructs a list recursively, inserting the sampled image of
zero and scanning the smaller list to apply the corresponding transposition.
The supplied equivalence is the complete duplicate-free enumeration of labels;
no enumeration is chosen and no favorable sample is selected.

The counted model charges one primitive uniform-finite draw per tape cell and
one transposition application per scanned tail entry. This is a primitive-draw
model, not a fair-bit implementation or a full machine-runtime theorem.
-/
namespace DirectedFlowCutGap.FinitePermutationSampler

open scoped BigOperators ENNReal

/-- A tape whose successive bounds are `n,n-1,...,1`; the empty tape is unique. -/
def Tape : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin (n + 1) × Tape n

instance tapeFintype : (n : ℕ) → Fintype (Tape n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (Fin (n + 1)) (Tape n) inferInstance (tapeFintype n)

instance tapeNonempty : (n : ℕ) → Nonempty (Tape n)
  | 0 => ⟨()⟩
  | n + 1 => ⟨(0, Classical.choice (tapeNonempty n))⟩

/-- The empty permutation is represented without a classical choice. -/
def emptyEquiv : Tape 0 ≃ Equiv.Perm (Fin 0) where
  toFun := fun _ => Equiv.refl _
  invFun := fun _ => ()
  left_inv := by intro t; cases t; rfl
  right_inv := by intro p; ext i; exact Fin.elim0 i

/-- Recursive transposition decoding is bijective, including the empty case. -/
def decode : (n : ℕ) → Tape n ≃ Equiv.Perm (Fin n)
  | 0 => emptyEquiv
  | n + 1 =>
      (Equiv.prodCongr (Equiv.refl _) (decode n)).trans Equiv.Perm.decomposeFin.symm

/-- Each scan consumes one list entry and applies the indicated transposition.
The second component counts the entries actually visited. -/
def scan {n : ℕ} (j : Fin (n + 1)) : List (Fin n) → List (Fin (n + 1)) × ℕ
  | [] => ([], 0)
  | x :: xs =>
      let r := scan j xs
      (Equiv.swap 0 j x.succ :: r.1, r.2 + 1)

@[simp] theorem scan_list {n : ℕ} (j : Fin (n + 1)) (xs : List (Fin n)) :
    (scan j xs).1 = xs.map (fun x => Equiv.swap 0 j x.succ) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scan, List.map_cons, ih]

@[simp] theorem scan_count {n : ℕ} (j : Fin (n + 1)) (xs : List (Fin n)) :
    (scan j xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scan, List.length_cons, ih]

/-- The executable result and the counts accumulated by that very execution. -/
structure Run (n : ℕ) where
  order : List (Fin n)
  draws : ℕ
  scans : ℕ
  deriving Repr

/-- Concrete recursive list interpreter. The singleton draw is charged too. -/
def run : (n : ℕ) → Tape n → Run n
  | 0, _ => ⟨[], 0, 0⟩
  | n + 1, (j, t) =>
      let r := run n t
      let q := scan j r.order
      ⟨j :: q.1, r.draws + 1, r.scans + q.2⟩

/-- Pointwise refinement of the list interpreter to the permutation bijection. -/
theorem run_order (n : ℕ) (t : Tape n) :
    (run n t).order = List.ofFn (decode n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases t with ⟨j, t⟩
      simp only [run, scan_list, ih, List.map_ofFn, List.ofFn_succ]
      congr 1
      · exact (Equiv.Perm.decomposeFin_symm_apply_zero j (decode n t)).symm
      · congr 1
        funext i
        exact (Equiv.Perm.decomposeFin_symm_apply_succ (decode n t) j i).symm

@[simp] theorem run_length (n : ℕ) (t : Tape n) : (run n t).order.length = n := by
  rw [run_order, List.length_ofFn]

@[simp] theorem run_draws (n : ℕ) (t : Tape n) : (run n t).draws = n := by
  induction n with
  | zero => rfl
  | succ n ih => rcases t with ⟨j, t⟩; simp [run, ih]

/-- This recurrence counts the literal tail entries visited, not an extensional
function whose evaluation work is left unaccounted for. -/
def scanBudget : ℕ → ℕ
  | 0 => 0
  | n + 1 => scanBudget n + n

@[simp] theorem run_scans (n : ℕ) (t : Tape n) : (run n t).scans = scanBudget n := by
  induction n with
  | zero => rfl
  | succ n ih => rcases t with ⟨j, t⟩; simp [run, ih, scanBudget]

theorem scanBudget_le_square (n : ℕ) : scanBudget n ≤ n * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scanBudget]; nlinarith

/-- A supplied enumeration is transported through the sampled permutation. -/
def labelPermutation {E : Type*} {n : ℕ} (enum : Fin n ≃ E) : Tape n ≃ Equiv.Perm E :=
  (decode n).trans (Equiv.permCongr enum)

/-- Express the computed order relative to any reference enumeration. This
reference may be used only in the proof and need not be computed at runtime. -/
def relativePermutation {E : Type*} {n : ℕ} (enum reference : Fin n ≃ E) :
    Tape n ≃ Equiv.Perm E :=
  (decode n).trans (Equiv.equivCongr reference enum)

/-- Materialize labels by one enumeration lookup per actual list entry. -/
def enumerate {E : Type*} {n : ℕ} (enum : Fin n ≃ E) : List (Fin n) → List E × ℕ
  | [] => ([], 0)
  | i :: is =>
      let r := enumerate enum is
      (enum i :: r.1, r.2 + 1)

@[simp] theorem enumerate_list {E : Type*} {n : ℕ} (enum : Fin n ≃ E)
    (is : List (Fin n)) : (enumerate enum is).1 = is.map enum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [enumerate, List.map_cons, ih]

@[simp] theorem enumerate_count {E : Type*} {n : ℕ} (enum : Fin n ≃ E)
    (is : List (Fin n)) : (enumerate enum is).2 = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [enumerate, List.length_cons, ih]

/-- Label output and work counters returned by a single shared execution. -/
structure LabelRun (E : Type*) where
  order : List E
  draws : ℕ
  scans : ℕ

/-- Run the permutation interpreter once, then materialize the labels once. -/
def labelRun {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) : LabelRun E :=
  let r := run n t
  let q := enumerate enum r.order
  ⟨q.1, r.draws, r.scans + q.2⟩

/-- Actual list output on the caller's complete duplicate-free enumeration. -/
def labelOrder {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) : List E :=
  (labelRun enum t).order

/-- Total executed transposition scans plus enumeration lookups, projected from
that same shared execution rather than recomputing the interpreter. -/
def labelScans {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) : ℕ :=
  (labelRun enum t).scans

@[simp] theorem labelRun_draws {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) :
    (labelRun enum t).draws = n := by simp [labelRun]

theorem labelScans_eq {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) :
    labelScans enum t = scanBudget n + n := by simp [labelScans, labelRun]

theorem labelScans_le {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) :
    labelScans enum t ≤ n * n + n := by
  rw [labelScans_eq]
  exact Nat.add_le_add_right (scanBudget_le_square n) n

theorem labelOrder_eq {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) :
    labelOrder enum t = List.ofFn (fun i => labelPermutation enum t (enum i)) := by
  simp [labelOrder, labelRun, run_order, List.map_ofFn, labelPermutation, Equiv.permCongr_def, Function.comp_def]

/-- Changing the analysis enumeration changes the permutation coordinate,
while the actually executed label list remains exactly the same. -/
theorem labelOrder_relative {E : Type*} {n : ℕ}
    (enum reference : Fin n ≃ E) (t : Tape n) :
    labelOrder enum t =
      List.ofFn (fun i => relativePermutation enum reference t (reference i)) := by
  simp [labelOrder, labelRun, run_order, List.map_ofFn, relativePermutation, Equiv.equivCongr, Function.comp_def]

theorem labelOrder_nodup {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) :
    (labelOrder enum t).Nodup := by
  rw [labelOrder_eq]
  exact List.nodup_ofFn.mpr ((labelPermutation enum t).injective.comp enum.injective)

theorem mem_labelOrder {E : Type*} {n : ℕ} (enum : Fin n ≃ E) (t : Tape n) (e : E) :
    e ∈ labelOrder enum t := by
  rw [labelOrder_eq, List.mem_ofFn]
  exact ⟨enum.symm ((labelPermutation enum t).symm e), by simp⟩

noncomputable section

/-- Independent sequencing of two finite laws, stated once for the tape proofs. -/
def independent {A B : Type*} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a => q.map fun b => (a, b)

@[simp] theorem independent_apply {A B : Type*} (p : PMF A) (q : PMF B) (ab : A × B) :
    independent p q ab = p ab.1 * q ab.2 := by
  classical
  rcases ab with ⟨a, b⟩
  have hm (a' : A) : (q.map (fun b' => (a', b'))) (a, b) =
      if a = a' then q b else 0 := by
    by_cases h : a = a'
    · subst a'
      simp [PMF.map_apply]
    · simp [PMF.map_apply, h]
  simp only [independent, PMF.bind_apply, hm, mul_ite, mul_zero]
  simp

/-- Sequencing two primitive uniform laws is uniform on the Cartesian product. -/
theorem independent_uniform {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] :
    independent (PMF.uniformOfFintype A) (PMF.uniformOfFintype B) =
      PMF.uniformOfFintype (A × B) := by
  apply PMF.ext
  intro ab
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod, ENNReal.mul_inv]

/-- A finite bijection takes exact uniform law to exact uniform law. -/
theorem uniform_map_equiv {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (e : A ≃ B) :
    (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply]
  have htest (a : A) : (b = e a) ↔ (e.symm b = a) := by
    exact ⟨fun h => by simpa using congrArg e.symm h,
      fun h => by simpa using congrArg e h⟩
  simp_rw [htest]
  simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- The actual primitive sampler: one new independent bounded draw per stage. -/
def tapePMF : (n : ℕ) → PMF (Tape n)
  | 0 => PMF.pure ()
  | n + 1 => independent (PMF.uniformOfFintype (Fin (n + 1))) (tapePMF n)

theorem tapePMF_uniform (n : ℕ) : tapePMF n = PMF.uniformOfFintype (Tape n) := by
  induction n with
  | zero =>
      apply PMF.ext
      intro t
      cases t
      change (PMF.pure () : PMF Unit) () = (PMF.uniformOfFintype Unit) ()
      simp [PMF.uniformOfFintype_apply]
  | succ n ih => rw [tapePMF, ih]; exact independent_uniform

/-- Exact uniform permutation law of the recursive primitive sampler. -/
theorem permutation_law (n : ℕ) :
    (tapePMF n).map (decode n) = PMF.uniformOfFintype (Equiv.Perm (Fin n)) := by
  rw [tapePMF_uniform]
  exact uniform_map_equiv (decode n)

/-- Exact uniform permutation law for an arbitrary supplied enumeration. -/
theorem labelPermutation_law {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} (enum : Fin n ≃ E) :
    (tapePMF n).map (labelPermutation enum) = PMF.uniformOfFintype (Equiv.Perm E) := by
  rw [tapePMF_uniform]
  exact uniform_map_equiv (labelPermutation enum)

/-- Uniformity is unchanged by a different reference enumeration. -/
theorem relativePermutation_law {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (enum reference : Fin n ≃ E) :
    (tapePMF n).map (relativePermutation enum reference) =
      PMF.uniformOfFintype (Equiv.Perm E) := by
  rw [tapePMF_uniform]
  exact uniform_map_equiv (relativePermutation enum reference)

/-- The same law governs the concrete finite list interpreter. -/
theorem labelOrder_law {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} (enum : Fin n ≃ E) :
    (tapePMF n).map (labelOrder enum) =
      (PMF.uniformOfFintype (Equiv.Perm E)).map (fun p => List.ofFn (fun i => p (enum i))) := by
  rw [← labelPermutation_law enum, PMF.map_comp]
  congr 1
  funext t
  exact labelOrder_eq enum t

end
end DirectedFlowCutGap.FinitePermutationSampler
