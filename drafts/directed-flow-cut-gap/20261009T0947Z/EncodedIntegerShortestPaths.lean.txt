import DirectedFlowCutGap.RetainedGridState

/-!
# Fully charged integer distances on a retained Boolean graph

The graph is a Boolean matrix and each weight is an entry in a retained array.
This module refines the existing bounded min-plus recurrence, preserving the
literal table order. Unlike its primitive-only counter, the counters here also
charge list cases, list/pair construction, sequencing, source comparisons and
array reads. Proofs and the ghost counters are erased. A scalar arithmetic or
comparison, tag operation, array read, or allocation of a fixed-size cell is
one word operation. The separate array materializer charges every copied cell;
no amortized growth or constant-time arbitrary callback is assumed.

These are mathematical instruction-model bounds. They do not formalize Lean's
compiler, allocator, garbage collector or the bit-level implementation of Nat.
-/
namespace DirectedFlowCutGap.EncodedIntegerShortestPaths
open RetainedGridState
open IntegerShortestPaths

variable {n : ℕ}

def graph (adjacency : PairFlags n) : Digraph (Fin n) where
  Adj u v := adjacency[u.val][v.val] = true

instance (adjacency : PairFlags n) : DecidableRel (graph adjacency).Adj :=
  fun u v => inferInstanceAs (Decidable (adjacency[u.val][v.val] = true))

/-- All primitive input access is visibly bounded: two adjacency reads, one
weight read and the source comparison. Each recursive branch retains its tail. -/
def scan (adjacency : PairFlags n) (a : Row n) (s u : Fin n) :
    Table (Fin n) → WithTop ℕ × ℕ
  | [] => (⊤, 1)
  | (v,d)::xs =>
      let r := scan adjacency a s u xs
      if (graph adjacency).Adj u v then
        (min ((((if u=s then 0 else a[u.val]) : ℕ) : WithTop ℕ) + d) r.1,
          r.2+20)
      else (r.1,r.2+8)

/-- The finite query scans the table once; it never recomputes the table. -/
def read (u : Fin n) : Table (Fin n) → WithTop ℕ × ℕ
  | [] => (⊤,1)
  | (v,d)::xs =>
      let r := read u xs
      if u=v then (min d r.1,r.2+8) else (r.1,r.2+5)

def initial (vs : List (Fin n)) (t : Fin n) : Table (Fin n) × ℕ :=
  (vs.map (fun v => (v,if v=t then 0 else ⊤)),6*vs.length+1)

def pass (adjacency : PairFlags n) (a : Row n) (s t : Fin n)
    (old : Table (Fin n)) : List (Fin n) → Table (Fin n) × ℕ
  | [] => ([],1)
  | u::us =>
      let q := scan adjacency a s u old
      let r := pass adjacency a s t old us
      ((u,min (if u=t then 0 else ⊤) q.1)::r.1,q.2+r.2+10)

def rounds (vs : List (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) : ℕ → Table (Fin n) × ℕ
  | 0 => initial vs t
  | k+1 =>
      let q := rounds vs adjacency a s t k
      let r := pass adjacency a s t q.1 vs
      (r.1,q.2+r.2+4)

def distance (E : Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) : WithTop ℕ × ℕ :=
  let N := E.vertices.length
  let q := rounds E.vertices adjacency a s t N
  let r := read s q.1
  (r.1,q.2+r.2+4*N+8)

theorem scan_value (adjacency : PairFlags n) (a : Row n) (s u : Fin n)
    (xs : Table (Fin n)) :
    (scan adjacency a s u xs).1 =
      (IntegerShortestPaths.scan (graph adjacency)
        (VertexGridDistances.outgoingNumerator (fun v => a[v.val]) s) u xs).1 := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
      rcases e with ⟨v,d⟩
      simp only [scan,IntegerShortestPaths.scan,VertexGridDistances.outgoingNumerator]
      split <;> simp only [ih]

theorem read_value (u : Fin n) (xs : Table (Fin n)) :
    (read u xs).1 = (IntegerShortestPaths.read u xs).1 := by
  induction xs with
  | nil => rfl
  | cons e xs ih => rcases e with ⟨v,d⟩; simp only [read,IntegerShortestPaths.read]; split <;> simp [ih]

theorem pass_value (adjacency : PairFlags n) (a : Row n) (s t : Fin n)
    (old : Table (Fin n)) (vs : List (Fin n)) :
    (pass adjacency a s t old vs).1 =
      (IntegerShortestPaths.pass (graph adjacency)
        (VertexGridDistances.outgoingNumerator (fun v => a[v.val]) s) t old vs).1 := by
  induction vs with
  | nil => rfl
  | cons u us ih => simp only [pass,IntegerShortestPaths.pass,scan_value,ih]

theorem rounds_value (vs : List (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) (k : ℕ) :
    (rounds vs adjacency a s t k).1 =
      (IntegerShortestPaths.rounds vs (graph adjacency)
        (VertexGridDistances.outgoingNumerator (fun v => a[v.val]) s) t k).1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rounds,IntegerShortestPaths.rounds,pass_value,ih]

theorem distance_value (E : Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) :
    (distance E adjacency a s t).1 =
      (IntegerLevelCuts.vertexDistance E (graph adjacency) (fun v => a[v.val]) s t).1 := by
  simp only [distance,IntegerLevelCuts.vertexDistance,IntegerShortestPaths.distance,
    read_value,rounds_value]

theorem scan_bound (adjacency : PairFlags n) (a : Row n) (s u : Fin n)
    (xs : Table (Fin n)) : (scan adjacency a s u xs).2 ≤ 20*xs.length+1 := by
  induction xs with
  | nil => simp [scan]
  | cons e xs ih => rcases e with ⟨v,d⟩; simp only [scan,List.length_cons]; split <;> omega

theorem read_bound (u : Fin n) (xs : Table (Fin n)) :
    (read u xs).2 ≤ 8*xs.length+1 := by
  induction xs with
  | nil => simp [read]
  | cons e xs ih => rcases e with ⟨v,d⟩; simp only [read,List.length_cons]; split <;> omega

@[simp] theorem pass_length (adjacency : PairFlags n) (a : Row n) (s t : Fin n)
    (old : Table (Fin n)) (vs : List (Fin n)) :
    (pass adjacency a s t old vs).1.length = vs.length := by
  rw [pass_value,IntegerShortestPaths.pass_length]

@[simp] theorem rounds_length (vs : List (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) (k : ℕ) : (rounds vs adjacency a s t k).1.length = vs.length := by
  rw [rounds_value,IntegerShortestPaths.rounds_length]

theorem pass_bound (adjacency : PairFlags n) (a : Row n) (s t : Fin n)
    (old : Table (Fin n)) (vs : List (Fin n)) :
    (pass adjacency a s t old vs).2 ≤ vs.length*(20*old.length+11)+1 := by
  induction vs with
  | nil => simp [pass]
  | cons u us ih =>
      have h := scan_bound adjacency a s u old
      simp only [pass,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem rounds_bound (vs : List (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) (k : ℕ) :
    (rounds vs adjacency a s t k).2 ≤
      6*vs.length+1+k*(vs.length*(20*vs.length+11)+5) := by
  induction k with
  | zero => simp [rounds,initial]
  | succ k ih =>
      have h := pass_bound adjacency a s t (rounds vs adjacency a s t k).1 vs
      rw [rounds_length] at h
      simp only [rounds,Nat.add_mul,Nat.one_mul]
      omega

def distanceBound (n : ℕ) : ℕ := 20*n^3+11*n^2+23*n+10

theorem distance_bound (E : Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) : (distance E adjacency a s t).2 ≤ distanceBound n := by
  have h := rounds_bound E.vertices adjacency a s t E.vertices.length
  have q := read_bound s (rounds E.vertices adjacency a s t E.vertices.length).1
  rw [rounds_length] at q
  rw [E.length_eq_card,Fintype.card_fin] at h q
  simp only [distance,E.length_eq_card,Fintype.card_fin]
  unfold distanceBound
  nlinarith

/-- Internal table numerators are bounded at every executed round, including
zero-weight paths and disconnected pairs. Infinity is a separate tag. -/
theorem table_within (vs : List (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) (k L : ℕ) (ha : ∀ v : Fin n, a[v.val] ≤ L) :
    ∀ e ∈ (rounds vs adjacency a s t k).1, IntegerShortestPaths.Within (k*L) e.2 := by
  rw [rounds_value]
  apply IntegerShortestPaths.rounds_within
  intro e
  simp only [VertexGridDistances.outgoingNumerator]
  split <;> [exact Nat.zero_le _; exact ha e.1]

theorem distance_within (E : Enumeration (Fin n)) (adjacency : PairFlags n) (a : Row n)
    (s t : Fin n) (L : ℕ) (ha : ∀ v : Fin n, a[v.val] ≤ L) :
    IntegerShortestPaths.Within (n*L) (distance E adjacency a s t).1 := by
  rw [distance_value]
  intro d hd
  have h := IntegerShortestPaths.distance_numerator_bound E (graph adjacency)
    (VertexGridDistances.outgoingNumerator (fun v => a[v.val]) s) L s t
    (by intro e; simp only [VertexGridDistances.outgoingNumerator]; split <;>
      [exact Nat.zero_le _; exact ha e.1]) d hd
  simpa only [E.length_eq_card,Fintype.card_fin] using h

/-- Maximum finite addition temporary, not merely the final answer. -/
theorem relaxation_width (k L x y : ℕ) (hx : x ≤ L) (hy : y ≤ k*L) :
    (x+y).size ≤ ((k+1)*L).size := by
  apply Nat.size_le_size
  nlinarith

end DirectedFlowCutGap.EncodedIntegerShortestPaths
