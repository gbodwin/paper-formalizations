import DirectedFlowCutGap.TabulatedIntegralFlow

/-!
# Counted finite search instructions

The supplied vertex list and Fintype enumeration are retained finite input
objects. Their construction is outside this module; the linear cardinality
read used for the search loop bound is charged here. Vertex equality is an
instruction on a fixed-arity encoded key. An arbitrary user-supplied equality
implementation is not assigned a complexity theorem by this interface.
Counters are ghost work annotations in this instruction model. This is not a
formal cost semantics for evaluating arbitrary Lean code or its instrumentation.
-/

namespace DirectedFlowCutGap.IntegralNetworkFlow.Tabulated
namespace CountedSearch

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A predicate instruction computes both its decision and its primitive-work
counter. No uncharged adjacency decision is called by the scan. -/
abbrev Test {α : Type*} (P : α → Prop) := (x : α) → Decidable (P x) × ℕ

/-- Each list case, option map, and result cell is charged as well as the test. -/
def scan {α : Type*} (P : α → Prop) (test : Test P) :
    (xs : List α) → Option {x : α // x ∈ xs ∧ P x} × ℕ
  | [] => (none,1)
  | x :: xs =>
    let a := test x
    match a.1 with
    | .isTrue h => (some ⟨x, by simp [h]⟩, a.2+8)
    | .isFalse _ =>
      let r := scan P test xs
      (r.1.map (fun y => ⟨y.1,List.mem_cons_of_mem x y.2.1,y.2.2⟩),a.2+8+r.2)

theorem scan_value {α : Type*} (P : α → Prop) [DecidablePred P]
    (test : Test P) (xs : List α) : (scan P test xs).1 = (ResidualSearch.scan P xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold scan
    dsimp only
    split
    · rename_i hp heq
      simp [ResidualSearch.scan, hp]
    · rename_i hp heq
      simp [ResidualSearch.scan, hp, ih]

theorem scan_bound {α : Type*} (P : α → Prop) (test : Test P)
    (C : ℕ) (ht : ∀ x, (test x).2 ≤ C) (xs : List α) :
    (scan P test xs).2 ≤ xs.length*(C+8)+1 := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    have h := ht x
    unfold scan
    dsimp only
    split <;> dsimp only <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega

variable {G : Digraph V} {t : V} [DecidableRel G.Adj]

def visit (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (S : ResidualSearch.State G t) (v : V) : ResidualSearch.State G t × ℕ :=
  let r := scan (fun e : ResidualSearch.Entry G t => e.1 = v)
    (fun e => (inferInstanceAs (Decidable (e.1=v)),1)) S.entries
  match hr : r.1 with
  | some _ => (S,r.2+4)
  | none =>
    let hv : v ∉ ResidualSearch.keys S.entries := by
      intro h
      obtain ⟨e,he,hev⟩ := ResidualSearch.mem_keys.mp h
      have hn : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=v) S.entries).1 = none :=
        (scan_value _ _ _).symm.trans hr
      exact ResidualSearch.scan_none _ _ hn e he hev
    let q := scan (fun e : ResidualSearch.Entry G t => G.Adj v e.1) (fun e => test v e.1) S.entries
    match q.1 with
    | none => (S,r.2+q.2+8)
    | some e => (S.add v hv e.1 e.2.1 e.2.2,r.2+q.2+16)

omit [Fintype V] in
theorem visit_value (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (S : ResidualSearch.State G t) (v : V) :
    (visit test S v).1 = (ResidualSearch.visit S v).1 := by
  unfold visit ResidualSearch.visit
  dsimp only
  split
  · rename_i e he
    have h : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=v) S.entries).1 = some e :=
      (scan_value _ _ _).symm.trans he
    split
    · rfl
    · rename_i hn
      have hbad := h.symm.trans hn
      cases hbad
  · rename_i he
    have h : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=v) S.entries).1 = none :=
      (scan_value _ _ _).symm.trans he
    symm
    split
    · rename_i e hh
      have hbad := h.symm.trans hh
      cases hbad
    · simp only [scan_value]
      cases (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => G.Adj v e.1) S.entries).1 <;> rfl

/-- All actual entry scans and constant-time path-prepend instructions are
covered; variable-time path vertex access is deferred until materialization. -/
def visitBound (N C : ℕ) : ℕ := N*(C+17)+18

omit [DecidableRel G.Adj] in
theorem visit_bound (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C)
    (S : ResidualSearch.State G t) (v : V) :
    (visit test S v).2 ≤ visitBound (Fintype.card V) C := by
  have he := scan_bound (fun e : ResidualSearch.Entry G t => e.1=v)
    (fun e => (inferInstanceAs (Decidable (e.1=v)),1)) 1 (by intros; exact Nat.le_refl _) S.entries
  have ha := scan_bound (fun e : ResidualSearch.Entry G t => G.Adj v e.1)
    (fun e => test v e.1) C (fun e => ht v e.1) S.entries
  have hl := S.length_le_card
  have hm₁ := Nat.mul_le_mul_right (1+8) hl
  have hm₂ := Nat.mul_le_mul_right (C+8) hl
  unfold visit
  dsimp only
  split
  · dsimp only
    unfold visitBound
    nlinarith
  · split <;> dsimp only <;> unfold visitBound <;> nlinarith

def pass (test : (u v : V) → Decidable (G.Adj u v) × ℕ) :
    List V → ResidualSearch.State G t → ResidualSearch.State G t × ℕ
  | [],S => (S,1)
  | v::vs,S =>
    let a := visit test S v
    let b := pass test vs a.1
    (b.1,a.2+b.2+4)

omit [Fintype V] in
theorem pass_value (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (vs : List V) (S : ResidualSearch.State G t) :
    (pass test vs S).1 = (ResidualSearch.pass vs S).1 := by
  induction vs generalizing S with
  | nil => rfl
  | cons v vs ih => simp only [pass, ResidualSearch.pass, ih, visit_value]

omit [DecidableRel G.Adj] in
theorem pass_bound (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C)
    (vs : List V) (S : ResidualSearch.State G t) :
    (pass test vs S).2 ≤ vs.length*(visitBound (Fintype.card V) C+4)+1 := by
  induction vs generalizing S with
  | nil => simp [pass]
  | cons v vs ih =>
    have ha := visit_bound test C ht S v
    have hb := ih (visit test S v).1
    simp only [pass, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def rounds (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) : ℕ → ResidualSearch.State G t × ℕ
  | 0 => (ResidualSearch.State.initial G t,8)
  | k+1 =>
    let a := rounds E test k
    let b := pass test E.vertices a.1
    (b.1,a.2+b.2+4)

omit [Fintype V] in
theorem rounds_value (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (k : ℕ) :
    (rounds E test k).1 = (ResidualSearch.rounds E.vertices G t k).1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rounds, ResidualSearch.rounds, pass_value, ih]

omit [DecidableRel G.Adj] in
theorem rounds_bound (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C) (k : ℕ) :
    (rounds (t := t) E test k).2 ≤
      k*(Fintype.card V*(visitBound (Fintype.card V) C+4)+5)+8 := by
  induction k with
  | zero => simp [rounds]
  | succ k ih =>
    have hb := pass_bound test C ht E.vertices (rounds (t := t) E test k).1
    rw [E.length_eq_card] at hb
    simp only [rounds, Nat.add_mul, Nat.one_mul]
    omega

/-- Lookup in a given complete table, separated to make dependent output
refinement independent of the table's construction proof. -/
def extract (S : ResidualSearch.State G t)
    (complete : ∀ (u : V), SimplePath G u t → u ∈ ResidualSearch.keys S.entries) (s : V) :
    ResidualSearch.Result G s t × ℕ :=
  let r := scan (fun e : ResidualSearch.Entry G t => e.1=s)
    (fun e => (inferInstanceAs (Decidable (e.1=s)),1)) S.entries
  match hr : r.1 with
  | some e => (.found (e.2.2 ▸ e.1.2),r.2+4)
  | none => (.stopped (by
      rintro ⟨p⟩
      obtain ⟨e,he,hes⟩ := ResidualSearch.mem_keys.mp (complete s p)
      have hn : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=s) S.entries).1 = none :=
        (scan_value _ _ _).symm.trans hr
      exact ResidualSearch.scan_none _ _ hn e he hes),r.2+4)

omit [Fintype V] [DecidableRel G.Adj] in
theorem extract_congr (S U : ResidualSearch.State G t)
    (hS : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys S.entries)
    (hU : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys U.entries)
    (s : V) (h : S=U) : (extract S hS s).1 = (extract U hU s).1 := by
  subst U
  rfl

theorem extract_searchTable (E : ResidualSearch.Enumeration V) (s t : V) :
    (extract (ResidualSearch.searchTable E G t).1
      (fun _ p => ResidualSearch.searchTable_complete E p) s).1 =
      (ResidualSearch.search E G s t).1 := by
  unfold extract ResidualSearch.search
  dsimp only
  split
  · rename_i e he
    have h : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=s)
        (ResidualSearch.searchTable E G t).1.entries).1 = some e :=
      (scan_value _ _ _).symm.trans he
    split
    · rename_i e' he'
      have heq : e=e' := Option.some.inj (h.symm.trans he')
      subst e'
      rfl
    · rename_i hn
      have hbad := h.symm.trans hn
      cases hbad
  · rename_i he
    have h : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=s)
        (ResidualSearch.searchTable E G t).1.entries).1 = none :=
      (scan_value _ _ _).symm.trans he
    split
    · rename_i e he'
      have hbad := h.symm.trans he'
      cases hbad
    · rfl

omit [DecidableRel G.Adj] in
theorem extract_bound (S : ResidualSearch.State G t)
    (complete : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys S.entries) (s : V) :
    (extract S complete s).2 ≤ 9*Fintype.card V+5 := by
  have hb := scan_bound (fun e : ResidualSearch.Entry G t => e.1=s)
    (fun e => (inferInstanceAs (Decidable (e.1=s)),1)) 1 (by intros; exact Nat.le_refl _) S.entries
  have hm := Nat.mul_le_mul_right (1+8) S.length_le_card
  unfold extract
  dsimp only
  split <;> dsimp only <;> omega

/-- Counted final source lookup, using precisely the same retained path table. -/
def search (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (s t : V) :
    ResidualSearch.Result G s t × ℕ :=
  let a := rounds (t := t) E test (Fintype.card V)
  let r := extract a.1 (by
    intro u p
    change u ∈ ResidualSearch.keys (rounds (t := t) E test (Fintype.card V)).1.entries
    rw [rounds_value]
    exact ResidualSearch.searchTable_complete E p) s
  (r.1,a.2+r.2+8*Fintype.card V+8)

theorem search_value (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (s t : V) :
    (search E test s t).1 = (ResidualSearch.search E G s t).1 := by
  change (extract (rounds (t := t) E test (Fintype.card V)).1 _ s).1 = _
  calc
    _ = (extract (ResidualSearch.searchTable E G t).1
        (fun _ p => ResidualSearch.searchTable_complete E p) s).1 :=
      extract_congr _ _ _ _ s (rounds_value E test _)
    _ = _ := extract_searchTable E s t

/-- Closed polynomial obtained from the actual instruction recurrence. -/
def searchBound (N C : ℕ) : ℕ := N*(N*(visitBound N C+4)+5)+17*N+21

theorem search_bound (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C) (s t : V) :
    (search E test s t).2 ≤ searchBound (Fintype.card V) C := by
  have ha := rounds_bound (t := t) E test C ht (Fintype.card V)
  have hb := extract_bound (rounds (t := t) E test (Fintype.card V)).1
    (by
      intro u p
      rw [rounds_value]
      exact ResidualSearch.searchTable_complete E p) s
  simp only [search]
  unfold searchBound
  omega

end CountedSearch
end DirectedFlowCutGap.IntegralNetworkFlow.Tabulated
