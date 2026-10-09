import DirectedFlowCutGap.EdgeModel
import DirectedFlowCutGap.ResidualPathSearch

/-!
# Executable bounded integer shortest paths

A synchronous min-plus recurrence over an explicitly supplied vertex list.
Each round materializes a new list of distances, so old computations are not
re-evaluated through nested function closures. Infinity is `WithTop Nat`.
The executed scans carry a primitive-operation counter: adjacency/equality,
minimum and extended-natural addition each count as one. List traversal and
allocation and integer bit costs are stated separately from this counter.
Evaluating the supplied cost function is also a separate input-access primitive;
it is called only for an adjacent table entry. An adjacency/equality test is
counted as one regardless of the supplied implementation's own running time.
Counter bookkeeping itself is excluded. Thus these are bounds for the listed
algorithmic primitive calls, not a full machine-time or bit-complexity claim.
-/
namespace DirectedFlowCutGap.IntegerShortestPaths

open scoped BigOperators NNReal ENNReal

variable {V : Type*} [DecidableEq V]

abbrev Enumeration := IntegralNetworkFlow.ResidualSearch.Enumeration
abbrev Table (V : Type*) := List (V × WithTop ℕ)

/-- Interpret an integer numerator as an exact grid distance, preserving infinity. -/
noncomputable def scaled (L : ℕ) : WithTop ℕ → ℝ≥0∞
  | none => ⊤
  | some n => ((n : ℝ≥0) / L : ℝ≥0)

@[simp] theorem scaled_top (L : ℕ) : scaled L ⊤ = ⊤ := rfl
@[simp] theorem scaled_coe (L n : ℕ) : scaled L (n : WithTop ℕ) =
    ((n : ℝ≥0) / L : ℝ≥0) := rfl
@[simp] theorem scaled_zero (L : ℕ) : scaled L 0 = 0 := by simp [scaled]

 theorem scaled_mono (L : ℕ) {a b : WithTop ℕ} (h : a ≤ b) :
    scaled L a ≤ scaled L b := by
  cases a using WithTop.recTopCoe with
  | top =>
    have hb : b = ⊤ := top_le_iff.mp h
    simp [hb]
  | coe a =>
    cases b using WithTop.recTopCoe with
    | top => exact le_top
    | coe b =>
      apply ENNReal.coe_le_coe.mpr
      apply div_le_div_of_nonneg_right _ bot_le
      exact_mod_cast h

@[simp] theorem scaled_min (L : ℕ) (a b : WithTop ℕ) :
    scaled L (min a b) = min (scaled L a) (scaled L b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (scaled_mono L h)]
  · rw [min_eq_right h, min_eq_right (scaled_mono L h)]

@[simp] theorem scaled_add_coe (L c : ℕ) (d : WithTop ℕ) :
    scaled L ((c : WithTop ℕ) + d) =
      (((c : ℝ≥0) / L : ℝ≥0) : ℝ≥0∞) + scaled L d := by
  cases d using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    change scaled L ((c+n : ℕ) : WithTop ℕ) = _
    rw [scaled_coe]
    simp only [Nat.cast_add, add_div, ENNReal.coe_add, scaled]

/-- Scan a materialized table for all possible first edges. -/
def scan (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → ℕ) (u : V) :
    Table V → WithTop ℕ × ℕ
  | [] => (⊤, 0)
  | (v, d) :: xs =>
      let r := scan G cost u xs
      if G.Adj u v then (min ((cost (u, v) : WithTop ℕ) + d) r.1, r.2 + 3)
      else (r.1, r.2 + 1)

/-- Query a key by a complete linear scan; duplicates, if supplied, use minimum. -/
def read (u : V) : Table V → WithTop ℕ × ℕ
  | [] => (⊤, 0)
  | (v, d) :: xs =>
      let r := read u xs
      if u = v then (min d r.1, r.2 + 2) else (r.1, r.2 + 1)

/-- The zero-edge table. -/
def initial (vs : List V) (t : V) : Table V × ℕ :=
  (vs.map (fun v => (v, if v = t then 0 else ⊤)), vs.length)

/-- Materialize one complete synchronous Bellman-Ford round. -/
def pass (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → ℕ)
    (t : V) (old : Table V) : List V → Table V × ℕ
  | [] => ([], 0)
  | u :: us =>
      let a := scan G cost u old
      let b := pass G cost t old us
      ((u, min (if u = t then 0 else ⊤) a.1) :: b.1, a.2 + 2 + b.2)

/-- Bounded recurrence: every round consumes the already computed previous table. -/
def rounds (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) : ℕ → Table V × ℕ
  | 0 => initial vs t
  | k + 1 =>
      let a := rounds vs G cost t k
      let b := pass G cost t a.1 vs
      (b.1, a.2 + b.2)

/-- The supplied enumeration determines both the data scans and the round bound. -/
def distance (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (s t : V) : WithTop ℕ × ℕ :=
  let r := rounds E.vertices G cost t E.vertices.length
  let q := read s r.1
  (q.1, r.2 + q.2)

@[simp] theorem pass_length (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) (old : Table V) (vs : List V) :
    (pass G cost t old vs).1.length = vs.length := by
  induction vs with
  | nil => rfl
  | cons u us ih => simp [pass, ih]

@[simp] theorem rounds_length (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) (k : ℕ) :
    (rounds vs G cost t k).1.length = vs.length := by
  cases k <;> simp [rounds, initial]

omit [DecidableEq V] in
 theorem scan_count_le (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (u : V) (xs : Table V) :
    (scan G cost u xs).2 ≤ 3 * xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons e xs ih =>
    rcases e with ⟨v,d⟩
    by_cases h : G.Adj u v <;> simp [scan, h, List.length_cons] <;> omega

 theorem read_count_le (u : V) (xs : Table V) :
    (read u xs).2 ≤ 2 * xs.length := by
  induction xs with
  | nil => simp [read]
  | cons e xs ih =>
    rcases e with ⟨v,d⟩
    by_cases h : u = v
    · subst v
      simp only [read, ite_true, List.length_cons]
      omega
    · simp only [read, h, ite_false, List.length_cons]
      omega

 theorem pass_count_le (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) (old : Table V) (vs : List V) :
    (pass G cost t old vs).2 ≤ vs.length * (3 * old.length + 2) := by
  induction vs with
  | nil => simp [pass]
  | cons u us ih =>
    have ha := scan_count_le G cost u old
    simp only [pass, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

 theorem rounds_count_le (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) (k : ℕ) :
    (rounds vs G cost t k).2 ≤ vs.length + k * vs.length * (3 * vs.length + 2) := by
  induction k with
  | zero => simp [rounds, initial]
  | succ k ih =>
    have hb := pass_count_le G cost t (rounds vs G cost t k).1 vs
    rw [rounds_length] at hb
    simp only [rounds, Nat.add_mul, Nat.one_mul]
    omega

/-- Bound for the counter returned by the executed algorithm, including query. -/
 theorem distance_count_le (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (s t : V) :
    (distance E G cost s t).2 ≤
      E.vertices.length ^ 2 * (3 * E.vertices.length + 2) + 3 * E.vertices.length := by
  have hr := rounds_count_le E.vertices G cost t E.vertices.length
  have hq := read_count_le s (rounds E.vertices G cost t E.vertices.length).1
  rw [rounds_length] at hq
  simp only [distance]
  nlinarith

 theorem read_le_of_mem (u : V) (xs : Table V) (d : WithTop ℕ)
    (h : (u,d) ∈ xs) : (read u xs).1 ≤ d := by
  induction xs with
  | nil => simp at h
  | cons e xs ih =>
    rcases e with ⟨v,a⟩
    rcases List.mem_cons.mp h with he | he
    · cases he
      simp [read]
    · have hh := ih he
      by_cases huv : u = v
      · simpa only [read, huv, ite_true] using
          (min_le_right a (read u xs).1).trans hh
      · simpa [read, huv] using hh

omit [DecidableEq V] in
 theorem scan_le_of_mem (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (u v : V) (xs : Table V) (d : WithTop ℕ)
    (hm : (v,d) ∈ xs) (ha : G.Adj u v) :
    (scan G cost u xs).1 ≤ (cost (u,v) : WithTop ℕ) + d := by
  induction xs with
  | nil => simp at hm
  | cons e xs ih =>
    rcases e with ⟨z,a⟩
    rcases List.mem_cons.mp hm with he | he
    · cases he
      simp [scan, ha]
    · have hh := ih he
      by_cases huz : G.Adj u z
      · simpa only [scan, huz, ite_true] using
          (min_le_right ((cost (u,z) : WithTop ℕ) + a) (scan G cost u xs).1).trans hh
      · simpa [scan, huz] using hh

 theorem mem_pass (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → ℕ)
    (t : V) (old : Table V) (vs : List V) (u : V) (hu : u ∈ vs) :
    (u, min (if u = t then 0 else ⊤) (scan G cost u old).1) ∈
      (pass G cost t old vs).1 := by
  induction vs with
  | nil => simp at hu
  | cons v vs ih =>
    rcases List.mem_cons.mp hu with rfl | hu
    · simp [pass]
    · exact List.mem_cons_of_mem _ (ih hu)

 theorem target_mem_rounds (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) (k : ℕ) :
    (t,0) ∈ (rounds E.vertices G cost t k).1 := by
  cases k with
  | zero => simp [rounds, initial, E.complete t]
  | succ k =>
    simpa [rounds] using
      mem_pass G cost t (rounds E.vertices G cost t k).1 E.vertices t (E.complete t)

/-- The computed self-distance is exactly zero, even with self-loops or zero weights. -/
 theorem distance_self (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) : (distance E G cost t t).1 = 0 := by
  apply le_antisymm _ bot_le
  exact read_le_of_mem t _ 0 (target_mem_rounds E G cost t E.vertices.length)

/-- Empty finite scans materialize no entries and incur zero counted operations. -/
 theorem rounds_empty (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) (k : ℕ) : rounds [] G cost t k = ([],0) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rounds, pass, ih]

/-- Every bounded directed sequence has a table value no larger than its integer cost. -/
 theorem rounds_sequence_le (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (t : V) (k n : ℕ) (v : Fin (n+1) → V)
    (ht : v (Fin.last n) = t)
    (ha : ∀ i : Fin n, G.Adj (v i.castSucc) (v i.succ)) (hn : n ≤ k) :
    ∃ d, (v 0,d) ∈ (rounds E.vertices G cost t k).1 ∧
      d ≤ ((∑ i : Fin n, cost (v i.castSucc, v i.succ) : ℕ) : WithTop ℕ) := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst n
    have hv : v 0 = t := ht
    exact ⟨0, by simpa only [hv] using target_mem_rounds E G cost t 0, by simp⟩
  | succ k ih =>
    cases n with
    | zero =>
      have hv : v 0 = t := ht
      exact ⟨0, by simpa only [hv] using target_mem_rounds E G cost t (k+1), by simp⟩
    | succ n =>
      obtain ⟨d, hd, hle⟩ := ih n (fun i => v i.succ) ht (fun i => ha i.succ)
        (by omega)
      let a := min (if v 0 = t then 0 else ⊤)
        (scan G cost (v 0) (rounds E.vertices G cost t k).1).1
      refine ⟨a, mem_pass G cost t _ E.vertices (v 0) (E.complete _), ?_⟩
      have hscan := scan_le_of_mem G cost (v 0) (v (Fin.succ 0))
        (rounds E.vertices G cost t k).1 d hd (ha 0)
      calc
        a ≤ (scan G cost (v 0) (rounds E.vertices G cost t k).1).1 := min_le_right _ _
        _ ≤ (cost (v 0, v (Fin.succ 0)) : WithTop ℕ) + d := hscan
        _ ≤ (cost (v 0, v (Fin.succ 0)) : WithTop ℕ) +
            ((∑ i : Fin n, cost (v i.succ.castSucc, v i.succ.succ) : ℕ) : WithTop ℕ) :=
          add_le_add_right hle _
        _ = _ := by rw [Fin.sum_univ_succ]; norm_cast

/-- The full scan preserves any lower bound for all its entries. -/
 theorem scaled_read_lower (L : ℕ) (u : V) (xs : Table V) (b : ℝ≥0∞)
    (h : ∀ d, (u,d) ∈ xs → b ≤ scaled L d) : b ≤ scaled L (read u xs).1 := by
  induction xs with
  | nil => simp [read]
  | cons e xs ih =>
    rcases e with ⟨v,d⟩
    have hh := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    by_cases huv : u = v
    · subst v
      simpa [read] using le_min (h d (by simp)) hh
    · simpa [read, huv] using hh

/-- Finite values are bounded; infinity is a separate tag and consumes no numerator. -/
def Within (B : ℕ) (d : WithTop ℕ) : Prop := ∀ n : ℕ, d = n → n ≤ B

 theorem within_top (B : ℕ) : Within B ⊤ := by simp [Within]
 theorem within_zero (B : ℕ) : Within B 0 := by
  intro n hn
  have h : (0 : ℕ) = n := WithTop.coe_injective hn
  omega
 theorem within_coe {B n : ℕ} (h : n ≤ B) : Within B (n : WithTop ℕ) := by
  intro m hm
  have : n = m := WithTop.coe_injective hm
  omega

 theorem within_mono {A B : ℕ} {d : WithTop ℕ} (h : Within A d) (hAB : A ≤ B) :
    Within B d := fun n hn => (h n hn).trans hAB

 theorem within_min {B : ℕ} {a b : WithTop ℕ} (ha : Within B a) (hb : Within B b) :
    Within B (min a b) := by
  rcases le_total a b with h | h
  · simpa [min_eq_left h] using ha
  · simpa [min_eq_right h] using hb

 theorem within_add {B C c : ℕ} {d : WithTop ℕ}
    (hc : c ≤ C) (hd : Within B d) : Within (C+B) ((c : WithTop ℕ) + d) := by
  cases d using WithTop.recTopCoe with
  | top => simpa using within_top (C+B)
  | coe n =>
    have hn := hd n rfl
    change Within (C+B) ((c+n : ℕ) : WithTop ℕ)
    exact within_coe (Nat.add_le_add hc hn)

omit [DecidableEq V] in
 theorem scan_within (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → ℕ)
    (B C : ℕ) (u : V) (xs : Table V) (hc : ∀ e, cost e ≤ C)
    (h : ∀ e ∈ xs, Within B e.2) : Within (C+B) (scan G cost u xs).1 := by
  induction xs with
  | nil => exact within_top _
  | cons e xs ih =>
    rcases e with ⟨v,d⟩
    have hh := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    by_cases ha : G.Adj u v
    · simpa only [scan, ha, ite_true] using
        within_min (within_add (hc (u,v)) (h (v,d) (by simp))) hh
    · simpa only [scan, ha, ite_false] using hh

 theorem pass_within (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → ℕ)
    (B C : ℕ) (t : V) (old : Table V) (vs : List V) (hc : ∀ e, cost e ≤ C)
    (h : ∀ e ∈ old, Within B e.2) :
    ∀ e ∈ (pass G cost t old vs).1, Within (C+B) e.2 := by
  induction vs with
  | nil => simp [pass]
  | cons u us ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · apply within_min _ (scan_within G cost B C u old hc h)
      split_ifs
      · exact within_zero _
      · exact within_top _
    · exact ih e he

/-- Every finite number materialized in round k has numerator at most k times
an upper bound on the input edge numerators. -/
 theorem rounds_within (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (C : ℕ) (t : V) (k : ℕ) (hc : ∀ e, cost e ≤ C) :
    ∀ e ∈ (rounds vs G cost t k).1, Within (k*C) e.2 := by
  induction k with
  | zero =>
    intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    split_ifs
    · exact within_zero _
    · exact within_top _
  | succ k ih =>
    simpa only [rounds, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
      pass_within G cost (k*C) C t (rounds vs G cost t k).1 vs hc ih

 theorem read_within (B : ℕ) (u : V) (xs : Table V)
    (h : ∀ e ∈ xs, Within B e.2) : Within B (read u xs).1 := by
  induction xs with
  | nil => exact within_top _
  | cons e xs ih =>
    rcases e with ⟨v,d⟩
    have hh := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    by_cases huv : u = v
    · simpa only [read, huv, ite_true] using within_min (h (v,d) (by simp)) hh
    · simpa only [read, huv, ite_false] using hh

 theorem distance_numerator_bound (E : Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → ℕ) (C : ℕ) (s t : V)
    (hc : ∀ e, cost e ≤ C) (d : ℕ) (hd : (distance E G cost s t).1 = d) :
    d ≤ E.vertices.length * C :=
  read_within _ s _ (rounds_within E.vertices G cost C t E.vertices.length hc) d hd

/-- Bit length of every finite returned numerator. Primitive Nat arithmetic,
input adjacency/equality and list allocation remain separately costed operations. -/
 theorem distance_bits_bound (E : Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → ℕ) (C : ℕ) (s t : V)
    (hc : ∀ e, cost e ≤ C) (d : ℕ) (hd : (distance E G cost s t).1 = d) :
    d.size ≤ (E.vertices.length*C).size :=
  Nat.size_le_size (distance_numerator_bound E G cost C s t hc d hd)

variable [Fintype V]

/-- Soundness follows from actual directed distance composition, proved from paths. -/
 theorem scan_sound (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → ℕ)
    (L : ℕ) (u t : V) (xs : Table V)
    (h : ∀ e ∈ xs, edgeDistance G (fun e => (cost e : ℝ≥0) / L) e.1 t ≤ scaled L e.2) :
    edgeDistance G (fun e => (cost e : ℝ≥0) / L) u t ≤ scaled L (scan G cost u xs).1 := by
  induction xs with
  | nil => simp [scan]
  | cons e xs ih =>
    rcases e with ⟨v,d⟩
    have hh := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    by_cases ha : G.Adj u v
    · simp only [scan, ha, ite_true, scaled_min, scaled_add_coe]
      apply le_min _ hh
      calc
        _ ≤ edgeDistance G (fun e => (cost e : ℝ≥0) / L) u v +
            edgeDistance G (fun e => (cost e : ℝ≥0) / L) v t :=
          edgeDistance_triangle _ _ _ _ _
        _ ≤ (((cost (u,v) : ℝ≥0) / L : ℝ≥0) : ℝ≥0∞) + scaled L d :=
          add_le_add (edgeDistance_le_of_adj _ ha) (h (v,d) (by simp))
    · simpa [scan, ha] using hh

 theorem pass_sound (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → ℕ)
    (L : ℕ) (t : V) (old : Table V) (vs : List V)
    (h : ∀ e ∈ old, edgeDistance G (fun e => (cost e : ℝ≥0) / L) e.1 t ≤ scaled L e.2) :
    ∀ e ∈ (pass G cost t old vs).1,
      edgeDistance G (fun e => (cost e : ℝ≥0) / L) e.1 t ≤ scaled L e.2 := by
  induction vs with
  | nil => simp [pass]
  | cons u us ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · simp only [scaled_min]
      apply le_min _ (scan_sound G cost L u t old h)
      by_cases hut : u = t
      · simp [hut]
      · simp [hut]
    · exact ih e he

 theorem rounds_sound (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (L : ℕ) (t : V) (k : ℕ) :
    ∀ e ∈ (rounds vs G cost t k).1,
      edgeDistance G (fun e => (cost e : ℝ≥0) / L) e.1 t ≤ scaled L e.2 := by
  induction k with
  | zero =>
    intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    by_cases h : v = t <;> simp [h]
  | succ k ih => exact pass_sound G cost L t _ vs ih

/-- Exact extended edge distance. No positivity assumption is imposed on edge costs. -/
 theorem distance_correct (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → ℕ) (L : ℕ) (s t : V) :
    scaled L (distance E G cost s t).1 =
      edgeDistance G (fun e => (cost e : ℝ≥0) / L) s t := by
  apply le_antisymm
  · rw [le_edgeDistance_iff]
    intro p
    obtain ⟨d, hd, hle⟩ := rounds_sequence_le E G cost t E.vertices.length
      p.edgeLength p.vertex p.target_eq p.adjacent (by
        rw [E.length_eq_card]
        exact Nat.le_of_lt p.edgeLength_lt_card)
    have hread := read_le_of_mem s (rounds E.vertices G cost t E.vertices.length).1 d
      (by simpa only [p.source_eq] using hd)
    calc
      _ ≤ scaled L ((∑ i : Fin p.edgeLength, cost (p.vertex i.castSucc, p.vertex i.succ) : ℕ) : WithTop ℕ) :=
        scaled_mono L (hread.trans hle)
      _ = (p.edgeWeight (fun e => (cost e : ℝ≥0) / L) : ℝ≥0∞) := by
        rw [scaled_coe, p.edgeWeight_eq_sum]
        congr 1
        simp only [SimplePath.edgeAt, ← Finset.sum_div, Nat.cast_sum]
  · exact scaled_read_lower L s _ _
      (fun d hd => rounds_sound E.vertices G cost L t E.vertices.length (s,d) hd)

end DirectedFlowCutGap.IntegerShortestPaths
