import DirectedFlowCutGap.IntegralMaxFlow

/-!
# Executable finite residual-path search

The input includes an explicit complete vertex list. A table stores actual simple
paths to the sink. Each pass scans that vertex list; a previously absent vertex
is inserted only when a table entry supplies an outgoing edge. The stored path
is extended with `SimplePath.prepend`, so no path enumeration or choice is used.

`scan` counts its predicate tests in the same recursion that computes its result.
`visit`, `pass`, and `rounds` retain and add these counters. This is an explicit
comparison/adjacency-query model, not a bit-complexity claim about integer flow
arithmetic or arbitrary implementations of vertex equality and adjacency.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow
namespace ResidualSearch

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An executable enumeration, supplied as data rather than chosen from finiteness. -/
structure Enumeration (V : Type*) where
  vertices : List V
  nodup : vertices.Nodup
  complete : ∀ v, v ∈ vertices

namespace Enumeration

/-- A supplied finite indexing gives an explicit list without choice. -/
def ofEquiv {n : ℕ} (e : Fin n ≃ V) : Enumeration V where
  vertices := List.ofFn e
  nodup := List.nodup_ofFn.mpr e.injective
  complete := by
    intro v
    exact List.mem_ofFn.mpr ⟨e.symm v, e.apply_symm_apply v⟩

/-- The standard enumeration of bounded natural-number vertices. -/
def fin (n : ℕ) : Enumeration (Fin n) := ofEquiv (Equiv.refl _)

theorem length_eq_card (E : Enumeration V) : E.vertices.length = Fintype.card V := by
  have h : E.vertices.toFinset = Finset.univ := by
    ext v
    simp [E.complete v]
  have hc := congrArg Finset.card h
  simpa [List.card_toFinset, E.nodup.dedup] using hc

end Enumeration

/-- A short-circuiting linear scan, returning its witness and exact test count. -/
def scan {α : Type*} (P : α → Prop) [DecidablePred P] :
    (xs : List α) → Option {x : α // x ∈ xs ∧ P x} × ℕ
  | [] => (none, 0)
  | x :: xs =>
      if h : P x then (some ⟨x, by simp [h]⟩, 1)
      else
        let r := scan P xs
        (r.1.map (fun y => ⟨y.1, List.mem_cons_of_mem x y.2.1, y.2.2⟩), r.2 + 1)

theorem scan_count_le {α : Type*} (P : α → Prop) [DecidablePred P] (xs : List α) :
    (scan P xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
      by_cases h : P x <;> simp only [scan, h, dite_true, dite_false, List.length_cons]
      · omega
      · exact Nat.add_le_add_right ih 1

theorem scan_none {α : Type*} (P : α → Prop) [DecidablePred P] (xs : List α)
    (h : (scan P xs).1 = none) : ∀ x ∈ xs, ¬P x := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      by_cases hy : P y
      · simp [scan, hy] at h
      · have hr : (scan P ys).1 = none := by
          simpa [scan, hy] using h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hy
        · exact ih hr x hx

abbrev Entry (G : Digraph V) (t : V) := Σ v, SimplePath G v t

def keys {G : Digraph V} {t : V} (xs : List (Entry G t)) : Finset V :=
  (xs.map Sigma.fst).toFinset

omit [Fintype V] in
@[simp] theorem mem_keys {G : Digraph V} {t v : V} {xs : List (Entry G t)} :
    v ∈ keys xs ↔ ∃ e ∈ xs, e.1 = v := by
  simp [keys]

omit [Fintype V] in
@[simp] theorem keys_nil {G : Digraph V} {t : V} :
    keys ([] : List (Entry G t)) = ∅ := rfl

omit [Fintype V] in
@[simp] theorem keys_cons {G : Digraph V} {t : V} (e : Entry G t)
    (xs : List (Entry G t)) : keys (e :: xs) = insert e.1 (keys xs) := by
  simp [keys]

/-- Every stored vertex has an actual path, whose vertices are already stored. -/
structure State (G : Digraph V) (t : V) where
  entries : List (Entry G t)
  unique : (entries.map Sigma.fst).Nodup
  support : ∀ e ∈ entries, e.2.vertices ⊆ keys entries

namespace State

variable {G : Digraph V} {t : V}

def initial (G : Digraph V) (t : V) : State G t where
  entries := [⟨t, SimplePath.refl G t⟩]
  unique := by simp
  support := by
    intro e he v hv
    simp only [List.mem_singleton] at he
    subst e
    obtain ⟨i, hi⟩ := (SimplePath.mem_vertices _ v).mp hv
    simp only [SimplePath.refl] at hi
    subst v
    simp

omit [Fintype V] in
@[simp] theorem initial_keys (G : Digraph V) (t : V) :
    keys (initial G t).entries = {t} := by simp [initial]

theorem length_le_card (S : State G t) : S.entries.length ≤ Fintype.card V := by
  have h := Finset.card_le_univ (keys S.entries)
  simpa [keys, List.card_toFinset, S.unique.dedup] using h

/-- Adding a new root extends one existing simple path by one genuine edge. -/
def add (S : State G t) (v : V) (hv : v ∉ keys S.entries)
    (e : Entry G t) (he : e ∈ S.entries) (ha : G.Adj v e.1) : State G t where
  entries := ⟨v, e.2.prepend ha (fun h => hv (S.support e he h))⟩ :: S.entries
  unique := by
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨by simpa [keys] using hv, S.unique⟩
  support := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [SimplePath.prepend_vertices, keys_cons]
      exact Finset.insert_subset_insert _ (S.support e he)
    · exact (S.support q hq).trans (by simp)

omit [Fintype V] in
@[simp] theorem add_keys (S : State G t) (v : V) (hv : v ∉ keys S.entries)
    (e : Entry G t) (he : e ∈ S.entries) (ha : G.Adj v e.1) :
    keys (S.add v hv e he ha).entries = insert v (keys S.entries) := by
  simp [add]

end State

variable {G : Digraph V} {t : V} [DecidableRel G.Adj]

/-- Two explicit table scans: first equality, then adjacency if the root is new. -/
def visit (S : State G t) (v : V) : State G t × ℕ :=
  let r := scan (fun e : Entry G t => e.1 = v) S.entries
  match hr : r.1 with
  | some _ => (S, r.2)
  | none =>
      let hv : v ∉ keys S.entries := by
        intro h
        obtain ⟨e, he, hev⟩ := mem_keys.mp h
        exact scan_none _ _ hr e he hev
      let q := scan (fun e : Entry G t => G.Adj v e.1) S.entries
      match q.1 with
      | none => (S, r.2 + q.2)
      | some e => (S.add v hv e.1 e.2.1 e.2.2, r.2 + q.2)

omit [Fintype V] in
theorem visit_mono (S : State G t) (v : V) :
    keys S.entries ⊆ keys (visit S v).1.entries := by
  unfold visit
  dsimp only
  split
  · exact Finset.Subset.refl _
  · split
    · exact Finset.Subset.refl _
    · simpa only [State.add_keys] using (Finset.subset_insert v (keys S.entries))

omit [Fintype V] in
theorem visit_edge (S : State G t) (u v : V) (hv : v ∈ keys S.entries)
    (ha : G.Adj u v) : u ∈ keys (visit S u).1.entries := by
  unfold visit
  dsimp only
  split
  · rename_i e he
    exact mem_keys.mpr ⟨e.1, e.2.1, e.2.2⟩
  · split
    · rename_i he hn
      obtain ⟨e, he, hev⟩ := mem_keys.mp hv
      exact (scan_none _ _ hn e he (by simpa only [hev] using ha)).elim
    · simp

theorem visit_count_le (S : State G t) (v : V) :
    (visit S v).2 ≤ 2 * Fintype.card V := by
  have h₁ := scan_count_le (fun e : Entry G t => e.1 = v) S.entries
  have h₂ := scan_count_le (fun e : Entry G t => G.Adj v e.1) S.entries
  have hn := S.length_le_card
  unfold visit
  dsimp only
  split
  · dsimp
    omega
  · split <;> dsimp <;> omega

/-- One full vertex-list pass. Earlier insertions are retained for later visits. -/
def pass : List V → State G t → State G t × ℕ
  | [], S => (S, 0)
  | v :: vs, S =>
      let a := visit S v
      let b := pass vs a.1
      (b.1, a.2 + b.2)

omit [Fintype V] in
theorem pass_mono (vs : List V) (S : State G t) :
    keys S.entries ⊆ keys (pass vs S).1.entries := by
  induction vs generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons v vs ih => exact (visit_mono S v).trans (ih (visit S v).1)

omit [Fintype V] in
theorem pass_edge (vs : List V) (S : State G t) (u v : V)
    (hu : u ∈ vs) (hv : v ∈ keys S.entries) (ha : G.Adj u v) :
    u ∈ keys (pass vs S).1.entries := by
  induction vs generalizing S with
  | nil => simp at hu
  | cons a vs ih =>
      rcases List.mem_cons.mp hu with rfl | hu
      · exact pass_mono vs (visit S u).1 (visit_edge S u v hv ha)
      · exact ih (visit S a).1 hu (visit_mono S a hv)

theorem pass_count_le (vs : List V) (S : State G t) :
    (pass vs S).2 ≤ vs.length * (2 * Fintype.card V) := by
  induction vs generalizing S with
  | nil => simp [pass]
  | cons v vs ih =>
      have ha := visit_count_le S v
      have hb := ih (visit S v).1
      simp only [pass, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- The counter is threaded through the actual state-producing recursion. -/
def rounds (vs : List V) (G : Digraph V) [DecidableRel G.Adj] (t : V) :
    ℕ → State G t × ℕ
  | 0 => (State.initial G t, 0)
  | k + 1 =>
      let a := rounds vs G t k
      let b := pass vs a.1
      (b.1, a.2 + b.2)

omit [Fintype V] in
theorem rounds_mono (vs : List V) (k : ℕ) :
    keys (rounds vs G t k).1.entries ⊆ keys (rounds vs G t (k+1)).1.entries :=
  pass_mono vs _

omit [Fintype V] in
theorem target_mem_rounds (vs : List V) (k : ℕ) :
    t ∈ keys (rounds vs G t k).1.entries := by
  induction k with
  | zero => simp [rounds]
  | succ k ih => exact rounds_mono vs k ih

omit [Fintype V] in
theorem rounds_cover (E : Enumeration V) (k : ℕ) {u : V}
    (p : SimplePath G u t) (hp : p.edgeLength ≤ k) :
    u ∈ keys (rounds E.vertices G t k).1.entries := by
  induction k generalizing u with
  | zero =>
      have hz : p.edgeLength = 0 := by omega
      have hut : u = t := by
        have hi : (0 : Fin (p.edgeLength+1)) = Fin.last p.edgeLength := by
          apply Fin.ext
          simpa using hz.symm
        exact p.source_eq.symm.trans ((congrArg p.vertex hi).trans p.target_eq)
      subst u
      exact target_mem_rounds E.vertices 0
  | succ k ih =>
      by_cases hz : p.edgeLength = 0
      · have hut : u = t := by
          have hi : (0 : Fin (p.edgeLength+1)) = Fin.last p.edgeLength := by
            apply Fin.ext
            simpa using hz.symm
          exact p.source_eq.symm.trans ((congrArg p.vertex hi).trans p.target_eq)
        subst u
        exact target_mem_rounds E.vertices (k+1)
      · let i : Fin (p.edgeLength+1) := ⟨1, by omega⟩
        let q := p.suffix i
        have hq : q.edgeLength ≤ k := by
          change p.edgeLength - 1 ≤ k
          omega
        have hv := ih q hq
        have ha : G.Adj u (p.vertex i) := by
          have h := p.adjacent ⟨0, by omega⟩
          simpa [i, p.source_eq] using h
        exact pass_edge E.vertices _ u (p.vertex i) (E.complete u) hv ha

theorem rounds_count_le (vs : List V) (k : ℕ) :
    (rounds vs G t k).2 ≤ k * vs.length * (2 * Fintype.card V) := by
  induction k with
  | zero => simp [rounds]
  | succ k ih =>
      have hb := pass_count_le vs (rounds vs G t k).1
      simp only [rounds, Nat.add_mul, Nat.one_mul]
      omega

/-- The final table and its explicit predicate-test count. -/
def searchTable (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj] (t : V) :=
  rounds E.vertices G t (Fintype.card V)

theorem searchTable_complete (E : Enumeration V) {u : V} (p : SimplePath G u t) :
    u ∈ keys (searchTable E G t).1.entries :=
  rounds_cover E _ p (Nat.le_of_lt p.edgeLength_lt_card)

/-- The computed reached set is backward closed under actual adjacency. -/
theorem searchTable_closed (E : Enumeration V) (u v : V)
    (hv : v ∈ keys (searchTable E G t).1.entries) (ha : G.Adj u v) :
    u ∈ keys (searchTable E G t).1.entries := by
  by_contra hu
  obtain ⟨e, he, hev⟩ := mem_keys.mp hv
  have ha' : G.Adj u e.1 := by simpa only [hev] using ha
  have hn : u ∉ e.2.vertices := fun h => hu ((searchTable E G t).1.support e he h)
  exact hu (searchTable_complete E (e.2.prepend ha' hn))

theorem mem_searchTable_iff (E : Enumeration V) (u : V) :
    u ∈ keys (searchTable E G t).1.entries ↔ Nonempty (SimplePath G u t) := by
  constructor
  · intro h
    obtain ⟨e, he, heu⟩ := mem_keys.mp h
    exact ⟨heu ▸ e.2⟩
  · rintro ⟨p⟩
    exact searchTable_complete E p

/-- The complement of sink-reachable vertices is an explicit forward-closed cut. -/
def separatingCut (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj] (t : V) :
    Finset V := (keys (searchTable E G t).1.entries)ᶜ

theorem separatingCut_closed (E : Enumeration V) (u v : V)
    (hu : u ∈ separatingCut E G t) (ha : G.Adj u v) :
    v ∈ separatingCut E G t := by
  rw [separatingCut, Finset.mem_compl] at hu ⊢
  intro hv
  exact hu (searchTable_closed E u v hv ha)

theorem source_mem_separatingCut (E : Enumeration V) (s : V)
    (h : ¬Nonempty (SimplePath G s t)) : s ∈ separatingCut E G t := by
  rw [separatingCut, Finset.mem_compl, mem_searchTable_iff]
  exact h

theorem target_not_mem_separatingCut (E : Enumeration V) :
    t ∉ separatingCut E G t := by
  rw [separatingCut, Finset.notMem_compl]
  exact target_mem_rounds E.vertices _

theorem searchTable_count_le (E : Enumeration V) :
    (searchTable E G t).2 ≤ 2 * (Fintype.card V)^3 := by
  have h := rounds_count_le (G := G) (t := t) E.vertices (Fintype.card V)
  rw [E.length_eq_card] at h
  simpa [searchTable, pow_succ, pow_zero, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

/-- A computed simple path or a checked absence certificate. -/
inductive Result (G : Digraph V) (s t : V) where
  | found (path : SimplePath G s t)
  | stopped (noPath : ¬Nonempty (SimplePath G s t))

/-- The final lookup is also the explicit counted linear scan. -/
def search (E : Enumeration V) (G : Digraph V) [DecidableRel G.Adj] (s t : V) :
    Result G s t × ℕ :=
  let a := searchTable E G t
  let r := scan (fun e : Entry G t => e.1 = s) a.1.entries
  match hr : r.1 with
  | some e => (.found (e.2.2 ▸ e.1.2), a.2 + r.2)
  | none =>
      (.stopped (by
        rintro ⟨p⟩
        obtain ⟨e, he, hes⟩ := mem_keys.mp (searchTable_complete E p)
        exact scan_none _ _ hr e he hes), a.2 + r.2)

theorem search_count_le (E : Enumeration V) (s : V) :
    (search E G s t).2 ≤ 2 * (Fintype.card V)^3 + Fintype.card V := by
  have ha := searchTable_count_le (G := G) (t := t) E
  have hr := scan_count_le (fun e : Entry G t => e.1 = s) (searchTable E G t).1.entries
  have hn := (searchTable E G t).1.length_le_card
  unfold search
  dsimp only
  split <;> dsimp <;> omega

end ResidualSearch

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Constructive residual search and the scan counter computed in that same run. -/
def finiteResidualSearchWithCost (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (f : Flow c s t) : PathSearchResult f × ℕ :=
  letI : DecidableRel f.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (f.amount u v < (c u v : ℤ)))
  let r := ResidualSearch.search E f.residual s t
  ((match r.1 with
    | .found p => .found p
    | .stopped h => .stopped h), r.2)

/-- The scan bound belongs to the executable result-producing wrapper itself. -/
theorem finiteResidualSearchWithCost_bound (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (f : Flow c s t) :
    (finiteResidualSearchWithCost E f).2 ≤ 2 * (Fintype.card V)^3 + Fintype.card V := by
  let : DecidableRel f.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (f.amount u v < (c u v : ℤ)))
  exact ResidualSearch.search_count_le E s

/-- Constructive residual search, with no classical choice in the executable body. -/
def finiteResidualSearch (E : ResidualSearch.Enumeration V)
    (c : Capacity V) (s t : V) : PathSearch c s t := fun f =>
  (finiteResidualSearchWithCost E f).1

/-- The finite complement table is the cut produced by residual search. -/
def finiteResidualCut (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (f : Flow c s t) : Finset V :=
  letI : DecidableRel f.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (f.amount u v < (c u v : ℤ)))
  ResidualSearch.separatingCut E f.residual t

/-- Optimality of the executable cut itself, rather than a classically chosen cut. -/
theorem finiteResidualCut_certificate (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (f : Flow c s t)
    (h : ¬Nonempty (SimplePath f.residual s t)) :
    s ∈ finiteResidualCut E f ∧ t ∉ finiteResidualCut E f ∧
      f.value = (cutCapacity c (finiteResidualCut E f) : ℤ) ∧
      (∀ g : Flow c s t, g.value ≤ f.value) ∧
      (∀ Y : Finset V, s ∈ Y → t ∉ Y →
        cutCapacity c (finiteResidualCut E f) ≤ cutCapacity c Y) := by
  let : DecidableRel f.residual.Adj := fun u v =>
    inferInstanceAs (Decidable (f.amount u v < (c u v : ℤ)))
  have hs := ResidualSearch.source_mem_separatingCut E s h
  have ht := ResidualSearch.target_not_mem_separatingCut (G := f.residual) (t := t) E
  have hc : ∀ u ∈ finiteResidualCut E f, ∀ v, f.residual.Adj u v →
      v ∈ finiteResidualCut E f := by
    intro u hu v ha
    exact ResidualSearch.separatingCut_closed E u v hu ha
  exact ⟨hs, ht, value_eq_cut_of_residual_closed f _ hs ht hc,
    (optimal_of_residual_closed f _ hs ht hc).1,
    (optimal_of_residual_closed f _ hs ht hc).2⟩

/-- Bounded augmentation instantiated with actual finite graph search. -/
theorem finiteResidualRun_certificate (E : ResidualSearch.Enumeration V)
    {c : Capacity V} {s t : V} (X : Finset V) (hs : s ∈ X) (ht : t ∉ X) :
    let f := run (finiteResidualSearch E c s t) (Flow.zero c s t) (cutCapacity c X)
    s ∈ finiteResidualCut E f ∧ t ∉ finiteResidualCut E f ∧
      f.value = (cutCapacity c (finiteResidualCut E f) : ℤ) ∧
      (∀ g : Flow c s t, g.value ≤ f.value) ∧
      (∀ Y : Finset V, s ∈ Y → t ∉ Y →
        cutCapacity c (finiteResidualCut E f) ≤ cutCapacity c Y) := by
  exact finiteResidualCut_certificate E _
    (run_stopped_at_cut_budget (finiteResidualSearch E c s t) X hs ht)

end DirectedFlowCutGap.IntegralNetworkFlow
