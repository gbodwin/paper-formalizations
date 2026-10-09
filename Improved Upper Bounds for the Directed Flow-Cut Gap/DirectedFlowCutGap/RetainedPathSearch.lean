import DirectedFlowCutGap.CountedResidualSearch

/-!
# Search with incrementally retained edge lists

The executable state carries a finite edge list beside each frozen search
entry. A newly reached root adds one actual edge-list cell to a retained tail.
Returned edges are read from this data table. No executable body evaluates a
SimplePath vertex function to materialize its edges: equality with the frozen
path edge list occurs only in proposition-valued invariant fields.

The word-instruction convention is inherited from CountedResidualSearch.
Root comparisons, list cases, result constructors, and predecessor-code reads
are charged; counters are ghost annotations, and supplied finite enumeration
data and equality dictionaries retain that module's explicit input contract.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.RetainedPathSearch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {t : V}

/-- A counted scan through retained roots and their edge-list data. -/
def readEdges (v : V) : List (V × List (V × V)) → List (V × V) × ℕ
  | [] => ([],0)
  | (u,es)::xs => if u=v then (es,1) else
    let r := readEdges v xs
    (r.1,r.2+1)

omit [Fintype V] in
theorem readEdges_bound (v : V) (xs : List (V × List (V × V))) :
    (readEdges v xs).2 ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨u,es⟩
    by_cases h : u=v <;> simp [readEdges,h,ih]

omit [Fintype V] in
theorem edgeList_prepend {s u t : V} (p : SimplePath G u t)
    (h : G.Adj s u) (hs : s ∉ p.vertices) :
    FlowTable.edgeList (p.prepend h hs) = (s,u) :: FlowTable.edgeList p := by
  unfold FlowTable.edgeList
  change List.ofFn (fun i : Fin (p.edgeLength+1) => (p.prepend h hs).edgeAt i) = _
  rw [List.ofFn_succ]
  congr 1
  change (s,p.vertex 0) = (s,u)
  rw [p.source_eq]

omit [Fintype V] [DecidableEq V] in
theorem edgeList_cast_source {s u t : V} (p : SimplePath G u t) (h : u=s) :
    FlowTable.edgeList (h ▸ p) = FlowTable.edgeList p := by
  subst s
  rfl

/-- Only finite list data are added to the frozen state. The path/code relation
is a proof field, so evaluating it cannot reintroduce coordinate computation. -/
structure State (G : Digraph V) (t : V) where
  legacy : ResidualSearch.State G t
  codes : List (V × List (V × V))
  keys_eq : codes.map Prod.fst = legacy.entries.map Sigma.fst
  coherent : ∀ e ∈ legacy.entries, (readEdges e.1 codes).1 = FlowTable.edgeList e.2

namespace State

def initial (G : Digraph V) (t : V) : State G t where
  legacy := ResidualSearch.State.initial G t
  codes := [(t,[])]
  keys_eq := rfl
  coherent := by
    intro e he
    simp only [ResidualSearch.State.initial,List.mem_singleton] at he
    subst e
    simp [readEdges,FlowTable.edgeList,SimplePath.refl]

theorem codes_length_le (S : State G t) : S.codes.length ≤ Fintype.card V := by
  have h := congrArg List.length S.keys_eq
  simp only [List.length_map] at h
  rw [h]
  exact S.legacy.length_le_card

/-- Retain the chosen predecessor's already materialized edges, prepend one
cell, and return the actual lookup work. -/
def addWithCost (S : State G t) (v : V) (hv : v ∉ ResidualSearch.keys S.legacy.entries)
    (e : ResidualSearch.Entry G t) (he : e ∈ S.legacy.entries) (ha : G.Adj v e.1) :
    State G t × ℕ :=
  let old := readEdges e.1 S.codes
  ({ legacy := S.legacy.add v hv e he ha
     codes := (v,(v,e.1)::old.1) :: S.codes
     keys_eq := by simpa only [List.map_cons,ResidualSearch.State.add] using congrArg (List.cons v) S.keys_eq
     coherent := by
       intro q hq
       change q ∈ _ :: S.legacy.entries at hq
       rcases List.mem_cons.mp hq with rfl | hq
       · simp only [readEdges,ite_true,edgeList_prepend]
         rw [S.coherent e he]
       · have hvq : v ≠ q.1 := by
           intro h
           exact hv (ResidualSearch.mem_keys.mpr ⟨q,hq,h.symm⟩)
         simp only [readEdges,hvq,ite_false]
         exact S.coherent q hq },8*old.2+16)

omit [Fintype V] in
@[simp] theorem addWithCost_legacy (S : State G t) (v : V)
    (hv : v ∉ ResidualSearch.keys S.legacy.entries)
    (e : ResidualSearch.Entry G t) (he : e ∈ S.legacy.entries) (ha : G.Adj v e.1) :
    (S.addWithCost v hv e he ha).1.legacy = S.legacy.add v hv e he ha := rfl

theorem addWithCost_bound (S : State G t) (v : V)
    (hv : v ∉ ResidualSearch.keys S.legacy.entries)
    (e : ResidualSearch.Entry G t) (he : e ∈ S.legacy.entries) (ha : G.Adj v e.1) :
    (S.addWithCost v hv e he ha).2 ≤ 8*Fintype.card V+16 := by
  have h := readEdges_bound e.1 S.codes
  have hl := S.codes_length_le
  change 8*(readEdges e.1 S.codes).2+16 ≤ _
  omega

end State

variable [DecidableRel G.Adj]

def visit (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (S : State G t) (v : V) : State G t × ℕ :=
  let r := CountedSearch.scan (fun e : ResidualSearch.Entry G t => e.1=v)
    (fun e => (inferInstanceAs (Decidable (e.1=v)),1)) S.legacy.entries
  match hr : r.1 with
  | some _ => (S,r.2+4)
  | none =>
    let hv : v ∉ ResidualSearch.keys S.legacy.entries := by
      intro h
      obtain ⟨e,he,hev⟩ := ResidualSearch.mem_keys.mp h
      have hn : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=v) S.legacy.entries).1 = none :=
        (CountedSearch.scan_value _ _ _).symm.trans hr
      exact ResidualSearch.scan_none _ _ hn e he hev
    let q := CountedSearch.scan (fun e : ResidualSearch.Entry G t => G.Adj v e.1)
      (fun e => test v e.1) S.legacy.entries
    match q.1 with
    | none => (S,r.2+q.2+8)
    | some e =>
      let a := S.addWithCost v hv e.1 e.2.1 e.2.2
      (a.1,r.2+q.2+a.2+8)

omit [Fintype V] [DecidableRel G.Adj] in
theorem visit_legacy (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (S : State G t) (v : V) :
    (visit test S v).1.legacy = (CountedSearch.visit test S.legacy v).1 := by
  unfold visit CountedSearch.visit
  dsimp only
  split
  · rename_i e he
    split
    · rfl
    · rename_i hn
      have hbad := he.symm.trans hn
      cases hbad
  · rename_i he
    symm
    split
    · rename_i e hh
      have hbad := he.symm.trans hh
      cases hbad
    · cases (CountedSearch.scan (fun e : ResidualSearch.Entry G t => G.Adj v e.1)
        (fun e => test v e.1) S.legacy.entries).1 <;> rfl

/-- Includes the predecessor-code lookup and the actual edge-list cons. -/
def visitBound (N C : ℕ) : ℕ := N*(C+32)+32

omit [DecidableRel G.Adj] in
theorem visit_bound (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C) (S : State G t) (v : V) :
    (visit test S v).2 ≤ visitBound (Fintype.card V) C := by
  have he := CountedSearch.scan_bound (fun e : ResidualSearch.Entry G t => e.1=v)
    (fun e => (inferInstanceAs (Decidable (e.1=v)),1)) 1 (by intros; exact Nat.le_refl _) S.legacy.entries
  have ha := CountedSearch.scan_bound (fun e : ResidualSearch.Entry G t => G.Adj v e.1)
    (fun e => test v e.1) C (fun e => ht v e.1) S.legacy.entries
  have hl := S.legacy.length_le_card
  have hm₁ := Nat.mul_le_mul_right 9 hl
  have hm₂ := Nat.mul_le_mul_right (C+8) hl
  unfold visit
  dsimp only
  split
  · dsimp only
    unfold visitBound
    nlinarith
  · rename_i hn
    split
    · dsimp only
      unfold visitBound
      nlinarith
    · rename_i e heq
      have hv : v ∉ ResidualSearch.keys S.legacy.entries := by
        intro h
        obtain ⟨a,ha,hav⟩ := ResidualSearch.mem_keys.mp h
        have hn' : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=v) S.legacy.entries).1 = none :=
          (CountedSearch.scan_value _ _ _).symm.trans hn
        exact ResidualSearch.scan_none _ _ hn' a ha hav
      have hb := S.addWithCost_bound v hv e.1 e.2.1 e.2.2
      dsimp only
      unfold visitBound
      nlinarith

def pass (test : (u v : V) → Decidable (G.Adj u v) × ℕ) :
    List V → State G t → State G t × ℕ
  | [],S => (S,1)
  | v::vs,S =>
    let a := visit test S v
    let b := pass test vs a.1
    (b.1,a.2+b.2+4)

omit [Fintype V] [DecidableRel G.Adj] in
theorem pass_legacy (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (vs : List V) (S : State G t) :
    (pass test vs S).1.legacy = (CountedSearch.pass test vs S.legacy).1 := by
  induction vs generalizing S with
  | nil => rfl
  | cons v vs ih => simp only [pass,CountedSearch.pass,ih,visit_legacy]

omit [DecidableRel G.Adj] in
theorem pass_bound (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C) (vs : List V) (S : State G t) :
    (pass test vs S).2 ≤ vs.length*(visitBound (Fintype.card V) C+4)+1 := by
  induction vs generalizing S with
  | nil => simp [pass]
  | cons v vs ih =>
    have ha := visit_bound test C ht S v
    have hb := ih (visit test S v).1
    simp only [pass,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def rounds (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) : ℕ → State G t × ℕ
  | 0 => (State.initial G t,16)
  | k+1 =>
    let a := rounds E test k
    let b := pass test E.vertices a.1
    (b.1,a.2+b.2+4)

omit [Fintype V] [DecidableRel G.Adj] in
theorem rounds_legacy (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (k : ℕ) :
    (rounds (t := t) E test k).1.legacy = (CountedSearch.rounds (t := t) E test k).1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rounds,CountedSearch.rounds,pass_legacy,ih]

omit [DecidableRel G.Adj] in
theorem rounds_bound (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C) (k : ℕ) :
    (rounds (t := t) E test k).2 ≤
      k*(Fintype.card V*(visitBound (Fintype.card V) C+4)+5)+16 := by
  induction k with
  | zero => simp [rounds]
  | succ k ih =>
    have hb := pass_bound test C ht E.vertices (rounds (t := t) E test k).1
    rw [E.length_eq_card] at hb
    simp only [rounds,Nat.add_mul,Nat.one_mul]
    omega

/-- The result retains edge data; its relation to the proof-carrying path is erased. -/
structure Result (G : Digraph V) (s t : V) where
  result : ResidualSearch.Result G s t
  edges : List (V × V)
  correct : match result with
    | .found p => edges = FlowTable.edgeList p
    | .stopped _ => edges = []
  work : ℕ

omit [DecidableRel G.Adj] in
theorem Result.edges_length_le {s : V} (r : Result G s t) :
    r.edges.length ≤ Fintype.card V := by
  cases h : r.result with
  | found p =>
    have he : r.edges = FlowTable.edgeList p := by simpa only [h] using r.correct
    rw [he,FlowTable.edgeList_length]
    exact Nat.le_of_lt p.edgeLength_lt_card
  | stopped hn =>
    have he : r.edges = [] := by simpa only [h] using r.correct
    simp [he]

/-- Source extraction reads the retained code, never the path's coordinate function. -/
def extract (S : State G t)
    (complete : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys S.legacy.entries) (s : V) :
    Result G s t :=
  let r := CountedSearch.scan (fun e : ResidualSearch.Entry G t => e.1=s)
    (fun e => (inferInstanceAs (Decidable (e.1=s)),1)) S.legacy.entries
  match hr : r.1 with
  | some e =>
    let a := readEdges s S.codes
    { result := .found (e.2.2 ▸ e.1.2)
      edges := a.1
      correct := by
        change (readEdges s S.codes).1 = FlowTable.edgeList (e.2.2 ▸ e.1.2)
        calc
          _ = (readEdges e.1.1 S.codes).1 := congrArg (fun v => (readEdges v S.codes).1) e.2.2.symm
          _ = FlowTable.edgeList e.1.2 := S.coherent e.1 e.2.1
          _ = _ := (edgeList_cast_source e.1.2 e.2.2).symm
      work := r.2+8*a.2+12 }
  | none =>
    { result := .stopped (by
        rintro ⟨p⟩
        obtain ⟨e,he,hes⟩ := ResidualSearch.mem_keys.mp (complete s p)
        have hn : (ResidualSearch.scan (fun e : ResidualSearch.Entry G t => e.1=s) S.legacy.entries).1 = none :=
          (CountedSearch.scan_value _ _ _).symm.trans hr
        exact ResidualSearch.scan_none _ _ hn e he hes)
      edges := []
      correct := rfl
      work := r.2+4 }

omit [Fintype V] [DecidableRel G.Adj] in
theorem extract_result (S : State G t)
    (complete : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys S.legacy.entries) (s : V) :
    (extract S complete s).result = (CountedSearch.extract S.legacy complete s).1 := by
  unfold extract CountedSearch.extract
  dsimp only
  split
  · rename_i e he
    split
    · rename_i e' he'
      have h : e=e' := Option.some.inj (he.symm.trans he')
      subst e'
      rfl
    · rename_i hn
      have h := he.symm.trans hn
      cases h
  · rename_i hn
    split
    · rename_i e he
      have h := hn.symm.trans he
      cases h
    · rfl

omit [DecidableRel G.Adj] in
theorem extract_bound (S : State G t)
    (complete : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys S.legacy.entries) (s : V) :
    (extract S complete s).work ≤ 17*Fintype.card V+13 := by
  have hs := CountedSearch.scan_bound (fun e : ResidualSearch.Entry G t => e.1=s)
    (fun e => (inferInstanceAs (Decidable (e.1=s)),1)) 1 (by intros; exact Nat.le_refl _) S.legacy.entries
  have hm := Nat.mul_le_mul_right 9 S.legacy.length_le_card
  have he := readEdges_bound s S.codes
  have hl := S.codes_length_le
  unfold extract
  dsimp only
  split <;> dsimp only <;> omega

def search (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (s t : V) : Result G s t :=
  let a := rounds (t := t) E test (Fintype.card V)
  let r := extract a.1 (by
    intro u p
    change u ∈ ResidualSearch.keys (rounds (t := t) E test (Fintype.card V)).1.legacy.entries
    rw [rounds_legacy,CountedSearch.rounds_value]
    exact ResidualSearch.searchTable_complete E p) s
  { result := r.result
    edges := r.edges
    correct := r.correct
    work := a.2+r.work+8*Fintype.card V+8 }

theorem search_result (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (s t : V) :
    (search E test s t).result = (ResidualSearch.search E G s t).1 := by
  change (extract (rounds (t := t) E test (Fintype.card V)).1 _ s).result = _
  rw [extract_result]
  calc
    _ = (CountedSearch.extract (ResidualSearch.searchTable E G t).1
        (fun _ p => ResidualSearch.searchTable_complete E p) s).1 :=
      CountedSearch.extract_congr _ _ _ _ s
        ((rounds_legacy E test _).trans (CountedSearch.rounds_value E test _))
    _ = _ := CountedSearch.extract_searchTable E s t

def searchBound (N C : ℕ) : ℕ := N*(N*(visitBound N C+4)+5)+25*N+37

theorem search_bound (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (C : ℕ) (ht : ∀ u v, (test u v).2 ≤ C) (s t : V) :
    (search E test s t).work ≤ searchBound (Fintype.card V) C := by
  have ha := rounds_bound (t := t) E test C ht (Fintype.card V)
  have hb := extract_bound (rounds (t := t) E test (Fintype.card V)).1
    (by
      intro u p
      rw [rounds_legacy,CountedSearch.rounds_value]
      exact ResidualSearch.searchTable_complete E p) s
  simp only [search]
  unfold searchBound
  omega

end DirectedFlowCutGap.IntegralNetworkFlow.Tabulated.RetainedPathSearch
