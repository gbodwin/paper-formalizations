import LightSpanners.UnitCycle
import LightSpanners.Counting

/-! Actual walk predicates for Definitions 5.2 and 5.4. These definitions permit
empty bucket blocks and require non-backtracking only inside each block.
No dispersion or hiker counting statement is assumed here. -/
namespace LightSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}

namespace UnitSpanningCycle
variable (C : UnitSpanningCycle G w)

/-- The ordered sequence of non-spanning-cycle edges in an actual walk. -/
noncomputable def chordEdges {u v : V} (p : G.Walk u v) : List (Sym2 V) :=
  p.edges.filter (fun e => e ∉ C.cycle.edges)

/-- The oriented spanning-cycle steps, with intervening chords removed. -/
noncomputable def cycleDarts {u v : V} (p : G.Walk u v) : List G.Dart :=
  p.darts.filter (fun d => d.edge ∈ C.cycle.edges)

/-- Structural part of bucket safety. Both directions are defined against
actual darts of the chosen oriented Hamiltonian cycle. -/
def BucketWalk {u v : V} (i s : ℕ) (p : G.Walk u v) : Prop :=
  p.edges.IsChain (· ≠ ·) ∧
  (∀ e ∈ C.chordEdges p, (2 : ℝ)^i ≤ w e ∧ w e < 2^(i+1)) ∧
  ∃ f b : List G.Dart, C.cycleDarts p = f ++ b ∧
    f.length = s ∧ b.length = s ∧
    (∀ d ∈ f, d ∈ C.cycle.darts) ∧ (∀ d ∈ b, d.symm ∈ C.cycle.darts)

def BucketSafe {u v : V} (eps : ℝ) (k i : ℕ) (p : G.Walk u v) : Prop :=
  ∃ s : ℕ, C.BucketWalk i s p ∧ (s : ℝ) ≤ eps * k * 2^i

def BucketExtraSafe {u v : V} (eps : ℝ) (k i : ℕ) (p : G.Walk u v) : Prop :=
  ∃ s : ℕ, C.BucketWalk i s p ∧ (s : ℝ) ≤ eps * k * 2^i / 2

@[simp] theorem chordEdges_nil (u : V) : C.chordEdges (.nil : G.Walk u u) = [] := rfl
@[simp] theorem cycleDarts_nil (u : V) : C.cycleDarts (.nil : G.Walk u u) = [] := rfl

@[simp] theorem chordEdges_append {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    C.chordEdges (p.append q) = C.chordEdges p ++ C.chordEdges q := by
  simp [chordEdges, Walk.edges_append]

@[simp] theorem cycleDarts_append {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    C.cycleDarts (p.append q) = C.cycleDarts p ++ C.cycleDarts q := by
  simp [cycleDarts, Walk.darts_append]

theorem bucketWalk_nil (i : ℕ) (u : V) : C.BucketWalk i 0 (.nil : G.Walk u u) := by
  exact ⟨List.isChain_nil, by simp, [], [], rfl, rfl, rfl, by simp, by simp⟩

theorem bucketSafe_nil (eps : ℝ) (heps : 0 ≤ eps) (k i : ℕ) (u : V) :
    C.BucketSafe eps k i (.nil : G.Walk u u) :=
  ⟨0, C.bucketWalk_nil i u, by simp only [Nat.cast_zero]; positivity⟩

theorem bucketExtraSafe_nil (eps : ℝ) (heps : 0 ≤ eps) (k i : ℕ) (u : V) :
    C.BucketExtraSafe eps k i (.nil : G.Walk u u) :=
  ⟨0, C.bucketWalk_nil i u, by simp only [Nat.cast_zero]; positivity⟩

theorem BucketExtraSafe.safe {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketExtraSafe eps k i p) : C.BucketSafe eps k i p := by
  obtain ⟨s, h, hs⟩ := h
  refine ⟨s, h, ?_⟩
  have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  linarith

theorem length_split {u v : V} (p : G.Walk u v) :
    p.length = (C.chordEdges p).length + (C.cycleDarts p).length := by
  induction p with
  | nil => simp
  | @cons u v z h p ih =>
    by_cases he : s(u,v) ∈ C.cycle.edges
    · simp [chordEdges, cycleDarts, Walk.edges_cons, Walk.darts_cons, he, ih,
        Nat.add_assoc, Nat.add_comm]
    · simp [chordEdges, cycleDarts, Walk.edges_cons, Walk.darts_cons, he, ih,
        Nat.add_comm, Nat.add_left_comm]

theorem BucketWalk.cycleDarts_length {u v : V} {i s : ℕ} {p : G.Walk u v}
    (h : C.BucketWalk i s p) : (C.cycleDarts p).length = 2*s := by
  obtain ⟨_, _, f, b, heq, hf, hb, _, _⟩ := h
  rw [heq, List.length_append, hf, hb]
  omega

theorem BucketSafe.cycle_budget {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketSafe eps k i p) :
    ((C.cycleDarts p).length : ℝ) ≤ 2*eps*k*2^i := by
  obtain ⟨s, hw, hs⟩ := h
  rw [hw.cycleDarts_length, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem BucketExtraSafe.cycle_budget {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketExtraSafe eps k i p) :
    ((C.cycleDarts p).length : ℝ) ≤ eps*k*2^i := by
  obtain ⟨s, hw, hs⟩ := h
  rw [hw.cycleDarts_length, Nat.cast_mul, Nat.cast_ofNat]
  linarith


/-- A weight budget on chords gives an actual walk-weight estimate; cycle
steps contribute exactly one each. -/
theorem walkWeight_le_chord_bound {u v : V} (p : G.Walk u v) (M : ℝ)
    (hM : ∀ e ∈ C.chordEdges p, w e ≤ M) :
    walkWeight w p ≤ (C.chordEdges p).length * M + (C.cycleDarts p).length := by
  induction p with
  | nil => simp [walkWeight]
  | @cons u v z h p ih =>
    have htail : ∀ e ∈ C.chordEdges p, w e ≤ M := by
      intro e he
      apply hM e
      simpa [chordEdges, Walk.edges_cons] using
        (show (e = s(u,v) ∨ e ∈ p.edges) ∧ e ∉ C.cycle.edges from
          ⟨Or.inr (List.mem_filter.mp he).1, by simpa using (List.mem_filter.mp he).2⟩)
    have hb := ih htail
    by_cases he : s(u,v) ∈ C.cycle.edges
    · have hw := C.unit _ he
      simp [walkWeight_cons, chordEdges, cycleDarts, Walk.edges_cons, Walk.darts_cons,
        he, hw, Nat.cast_add, Nat.cast_one] at ⊢
      simpa [chordEdges, cycleDarts, add_assoc, add_comm, add_left_comm] using add_le_add_left hb 1
    · have hw := hM s(u,v) (by simp [chordEdges, Walk.edges_cons, he])
      simp [walkWeight_cons, chordEdges, cycleDarts, Walk.edges_cons, Walk.darts_cons,
        he, Nat.cast_add, Nat.cast_one] at ⊢
      simp [chordEdges, cycleDarts] at hb
      nlinarith

theorem BucketSafe.weight_budget {u v : V} {eps : ℝ} {k i : ℕ} {p : G.Walk u v}
    (h : C.BucketSafe eps k i p) :
    walkWeight w p ≤ (C.chordEdges p).length * 2^(i+1) + 2*eps*k*2^i := by
  have hc := h.cycle_budget
  obtain ⟨s, hp, _⟩ := h
  have hw := C.walkWeight_le_chord_bound p (2^(i+1)) (fun e he => (hp.2.1 e he).2.le)
  linarith

/-- Concatenation in increasing bucket order. Empty blocks are allowed, and
no non-backtracking condition is imposed across block boundaries. -/
inductive BucketMonotoneWalk (eps : ℝ) (k : ℕ) (extra : Bool) :
    ℕ → {u v : V} → G.Walk u v → Prop
  | nil (u : V) : BucketMonotoneWalk eps k extra 0 (.nil : G.Walk u u)
  | snoc {j : ℕ} {u v z : V} {p : G.Walk u v} {q : G.Walk v z}
      (hp : BucketMonotoneWalk eps k extra j p)
      (hq : if extra then C.BucketExtraSafe eps k j q else C.BucketSafe eps k j q) :
      BucketMonotoneWalk eps k extra (j+1) (p.append q)

/-- Definition 5.4, with exactly k non-cycle edges. The bucket decomposition
is a proposition witnessing actual concatenated graph walks. -/
def BucketMonotoneKPath {u v : V} (eps : ℝ) (k : ℕ) (extra : Bool)
    (p : G.Walk u v) : Prop :=
  (C.chordEdges p).length = k ∧ ∃ j, C.BucketMonotoneWalk eps k extra j p

theorem BucketMonotoneWalk.forget_extra {eps : ℝ} {k j : ℕ} {u v : V}
    {p : G.Walk u v} (h : C.BucketMonotoneWalk eps k true j p) :
    C.BucketMonotoneWalk eps k false j p := by
  induction h with
  | nil u => exact .nil u
  | snoc hp hq ih => exact .snoc ih (BucketExtraSafe.safe C hq)

theorem BucketMonotoneKPath.forget_extra {eps : ℝ} {k : ℕ} {u v : V}
    {p : G.Walk u v} (h : C.BucketMonotoneKPath eps k true p) :
    C.BucketMonotoneKPath eps k false p := by
  obtain ⟨hk, j, hj⟩ := h
  exact ⟨hk, j, hj.forget_extra⟩

end UnitSpanningCycle
end LightSpanners
