import DirectedFlowCutGap.BinaryFractionalRows
import DirectedFlowCutGap.FractionalCoverRawOracle
import DirectedFlowCutGap.EncodedArrayStorage

/-!
# Binary rational bounded walks and retained simple paths

All path-cost fields are actual Boolean-list fractions. Relaxation, comparison,
and recovery summation call the binary rational routines and retain their
computed results and charges. The outer relaxation loop consumes the retained
vertex list, with no numerical denotation controlling execution. Exact
refinement includes the chosen edge list and both unreduced fraction fields;
there is no assumption supplying a favorable path or an optimal column.

Graph labels and Boolean adjacency use the existing finite-data instruction
model. Simple-path recovery reuses its checked retained support search and
its explicit instruction charge. Heap addresses and the realization of label
operations belong to the shared storage/runtime layer, not this module.
-/
namespace DirectedFlowCutGap.BinaryFractionalWalkOracle
open BinaryRational
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

variable {n : ℕ}
abbrev Pair (n : ℕ) := Fin n × Fin n
abbrev Adjacency (n : ℕ) := Vector (Vector Bool n) n
abbrev Cost (n : ℕ) := Pair n → Fraction × ℕ

abbrev graph (adjacency : Adjacency n) := EncodedIntegerShortestPaths.graph adjacency

/-- Two retained matrix reads use the shared storage callback. -/
def adjacent (adjacency : Adjacency n) (u v : Fin n) : Bool × ℕ :=
  let row := EncodedArrayStorage.readCallback adjacency u
  let cell := EncodedArrayStorage.readCallback row.1 v
  (cell.1,row.2+cell.2+4)

@[simp] theorem adjacent_value (adjacency : Adjacency n) (u v : Fin n) :
    (adjacent adjacency u v).1=true ↔ (graph adjacency).Adj u v := Iff.rfl

def decodeCost (cost : Cost n) (e : Pair n) : RawNonnegativeRational.Code :=
  BinaryRational.decode (cost e).1

structure Candidate (n : ℕ) where
  edges : List (Pair n)
  cost : Fraction

abbrev Table (n : ℕ) := List (Fin n × Candidate n)

def decode (q : Candidate n) : FractionalCoverRawOracle.Candidate (Fin n) :=
  ⟨q.edges,BinaryRational.decode q.cost⟩

def decodeTable (xs : Table n) : FractionalCoverRawOracle.Table (Fin n) :=
  xs.map (fun q => (q.1,decode q.2))

def zero : Candidate n := ⟨[],BinaryRational.zero⟩

def extend (cost : Cost n) (u v : Fin n) (q : Candidate n) : Candidate n × ℕ :=
  let w := cost (u,v)
  let a := BinaryRational.add w.1 q.cost
  (⟨(u,v)::q.edges,a.1⟩,w.2+a.2+8)

@[simp] theorem decode_zero : decode (zero : Candidate n) = FractionalCoverRawOracle.zero := rfl

@[simp] theorem extend_decode (cost : Cost n) (u v : Fin n) (q : Candidate n) :
    decode (extend cost u v q).1 =
      FractionalCoverRawOracle.extend (decodeCost cost) u v (decode q) := by
  simp [extend,decode,decodeCost,FractionalCoverRawOracle.extend]

/-- Ties keep the left candidate, exactly as in the frozen raw recurrence. -/
def pick : Option (Candidate n) → Option (Candidate n) → Option (Candidate n) × ℕ
  | none,b => (b,4)
  | a,none => (a,4)
  | some a,some b =>
    let c := BinaryRational.le a.cost b.cost
    (if c.1 then some a else some b,c.2+6)

theorem pick_decode (a b : Option (Candidate n)) :
    (pick a b).1.map decode = FractionalCoverRawOracle.pick (a.map decode) (b.map decode) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      simp only [pick,FractionalCoverRawOracle.pick,Option.map_some,decode,le_decode]
      split_ifs <;> rfl

def scan (adjacency : Adjacency n) (cost : Cost n) (u : Fin n) :
    Table n → Option (Candidate n) × ℕ
  | [] => (none,1)
  | (v,q)::xs =>
    let r := scan adjacency cost u xs
    let edge := adjacent adjacency u v
    if edge.1 then
      let a := extend cost u v q
      let b := pick (some a.1) r.1
      (b.1,r.2+edge.2+a.2+b.2+12)
    else (r.1,r.2+edge.2+8)

theorem scan_decode (adjacency : Adjacency n) (cost : Cost n) (u : Fin n) (xs : Table n) :
    (scan adjacency cost u xs).1.map decode =
      (FractionalCoverRawOracle.scan (graph adjacency) (decodeCost cost) u (decodeTable xs)).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨v,q⟩
    by_cases h : (graph adjacency).Adj u v <;>
      simp [scan,FractionalCoverRawOracle.scan,decodeTable,h,pick_decode,ih]

def atVertex (adjacency : Adjacency n) (cost : Cost n)
    (t u : Fin n) (old : Table n) : Option (Candidate n) × ℕ :=
  if u=t then (some zero,6) else
    let r := scan adjacency cost u old
    (r.1,r.2+6)

theorem atVertex_decode (adjacency : Adjacency n) (cost : Cost n)
    (t u : Fin n) (old : Table n) :
    (atVertex adjacency cost t u old).1.map decode =
      (FractionalCoverRawOracle.atVertex (graph adjacency) (decodeCost cost) t u (decodeTable old)).1 := by
  by_cases h : u=t <;>
    simp [atVertex,FractionalCoverRawOracle.atVertex,h,scan_decode]

def pass (adjacency : Adjacency n) (cost : Cost n) (t : Fin n) (old : Table n) :
    List (Fin n) → Table n × ℕ
  | [] => ([],1)
  | u::us =>
    let r := atVertex adjacency cost t u old
    let tail := pass adjacency cost t old us
    match r.1 with
    | none => (tail.1,r.2+tail.2+6)
    | some q => ((u,q)::tail.1,r.2+tail.2+10)

theorem pass_decode (adjacency : Adjacency n) (cost : Cost n)
    (t : Fin n) (old : Table n) (vs : List (Fin n)) :
    decodeTable (pass adjacency cost t old vs).1 =
      (FractionalCoverRawOracle.pass (graph adjacency) (decodeCost cost) t (decodeTable old) vs).1 := by
  induction vs with
  | nil => rfl
  | cons u us ih =>
    have h := atVertex_decode adjacency cost t u old
    cases hr : (atVertex adjacency cost t u old).1 with
    | none =>
      simp only [pass,FractionalCoverRawOracle.pass,← h,hr,Option.map_none]
      exact ih
    | some q =>
      simp only [pass,FractionalCoverRawOracle.pass,← h,hr,Option.map_some]
      exact congrArg (List.cons (u,decode q)) ih

/-- Both iteration order and retained table order match the existing program. -/
def rounds (vs : List (Fin n)) (adjacency : Adjacency n) (cost : Cost n) (t : Fin n) :
    List (Fin n) → Table n × ℕ
  | [] => ([(t,zero)],8)
  | _::rest =>
    let old := rounds vs adjacency cost t rest
    let next := pass adjacency cost t old.1 vs
    (next.1,old.2+next.2+6)

theorem rounds_decode (vs : List (Fin n)) (adjacency : Adjacency n) (cost : Cost n)
    (t : Fin n) (fuel : List (Fin n)) :
    decodeTable (rounds vs adjacency cost t fuel).1 =
      (FractionalCoverRawOracle.rounds vs (graph adjacency) (decodeCost cost) t fuel.length).1 := by
  induction fuel with
  | nil => rfl
  | cons u us ih =>
    simp only [rounds,List.length_cons,FractionalCoverRawOracle.rounds,pass_decode,ih]

def lookup (u : Fin n) : Table n → Option (Candidate n) × ℕ
  | [] => (none,1)
  | (v,q)::xs =>
    let tail := lookup u xs
    if u=v then
      let p := pick (some q) tail.1
      (p.1,tail.2+p.2+6)
    else (tail.1,tail.2+6)

theorem lookup_decode (u : Fin n) (xs : Table n) :
    (lookup u xs).1.map decode = (FractionalCoverRawOracle.lookup u (decodeTable xs)).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨v,q⟩
    by_cases h : u=v
    · subst v
      simp only [lookup,FractionalCoverRawOracle.lookup,decodeTable,List.map_cons,
        ite_true,pick_decode,Option.map_some]
      exact congrArg (FractionalCoverRawOracle.pick (some (decode q))) ih
    · simp only [lookup,FractionalCoverRawOracle.lookup,decodeTable,List.map_cons,h,ite_false]
      exact ih

def minimize (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (s t : Fin n) : Option (Candidate n) × ℕ :=
  let table := rounds E.vertices adjacency cost t E.vertices
  let r := lookup s table.1
  (r.1,table.2+r.2+8*E.vertices.length+8)

theorem minimize_decode (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (s t : Fin n) :
    (minimize E adjacency cost s t).1.map decode =
      (FractionalCoverRawOracle.minimize E (graph adjacency) (decodeCost cost) s t).1 := by
  simp only [minimize,FractionalCoverRawOracle.minimize,lookup_decode,rounds_decode]

/-- Read every recovered edge's actual fraction exactly once into a retained list. -/
def costList (cost : Cost n) : List (Pair n) → List Fraction × ℕ
  | [] => ([],1)
  | e::es =>
    let q := cost e
    let tail := costList cost es
    (q.1::tail.1,q.2+tail.2+6)

theorem costList_decode (cost : Cost n) (es : List (Pair n)) :
    (costList cost es).1.map BinaryRational.decode = es.map (decodeCost cost) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [costList,decodeCost,ih]

/-- Explicit membership scan for the recovery subgraph. -/
def memberEdge (e : Pair n) : List (Pair n) → Bool × ℕ
  | [] => (false,1)
  | a::as => if a=e then (true,8) else
    let r := memberEdge e as
    (r.1,r.2+8)

theorem memberEdge_spec (e : Pair n) (es : List (Pair n)) :
    (memberEdge e es).1=true ↔ e ∈ es := by
  induction es with
  | nil => simp [memberEdge]
  | cons a as ih =>
    by_cases h : a=e
    · subst a
      simp [memberEdge]
    · simp [memberEdge,h,Ne.symm h,ih]

/-- The support callback pays the concrete matrix reads and membership scan. -/
def supportTest (adjacency : Adjacency n) (es : List (Pair n)) (u v : Fin n) :
    Decidable ((FractionalCoverPathOracle.supportGraph (graph adjacency) es).Adj u v) × ℕ :=
  let a := adjacent adjacency u v
  let m := memberEdge (u,v) es
  if h : (a.1 && m.1)=true then
    (isTrue ⟨(adjacent_value adjacency u v).mp (Bool.and_eq_true_iff.mp h).1,
      (memberEdge_spec (u,v) es).mp (Bool.and_eq_true_iff.mp h).2⟩,a.2+m.2+8)
  else
    (isFalse (fun hg => h (Bool.and_eq_true_iff.mpr
      ⟨(adjacent_value adjacency u v).mpr hg.1,(memberEdge_spec (u,v) es).mpr hg.2⟩)),a.2+m.2+8)

/-- Changing a test's charge cannot change the selected retained predecessor. -/
theorem visit_state_independent {G : Digraph (Fin n)} [DecidableRel G.Adj] {t : Fin n}
    (a b : (u v : Fin n) → Decidable (G.Adj u v) × ℕ)
    (S : RetainedPathSearch.State G t) (v : Fin n) :
    (RetainedPathSearch.visit a S v).1=(RetainedPathSearch.visit b S v).1 := by
  have hq : (CountedSearch.scan (fun e : ResidualSearch.Entry G t => G.Adj v e.1)
      (fun e => a v e.1) S.legacy.entries).1 =
    (CountedSearch.scan (fun e : ResidualSearch.Entry G t => G.Adj v e.1)
      (fun e => b v e.1) S.legacy.entries).1 :=
    (CountedSearch.scan_value _ _ _).trans (CountedSearch.scan_value _ _ _).symm
  unfold RetainedPathSearch.visit
  dsimp only
  split
  · rfl
  · simp only [hq]
    split <;> rfl

theorem pass_state_independent {G : Digraph (Fin n)} [DecidableRel G.Adj] {t : Fin n}
    (a b : (u v : Fin n) → Decidable (G.Adj u v) × ℕ)
    (vs : List (Fin n)) (S : RetainedPathSearch.State G t) :
    (RetainedPathSearch.pass a vs S).1=(RetainedPathSearch.pass b vs S).1 := by
  induction vs generalizing S with
  | nil => rfl
  | cons v vs ih =>
    simp only [RetainedPathSearch.pass,ih,visit_state_independent a b S v]

theorem rounds_state_independent {G : Digraph (Fin n)} [DecidableRel G.Adj] {t : Fin n}
    (E : ResidualSearch.Enumeration (Fin n))
    (a b : (u v : Fin n) → Decidable (G.Adj u v) × ℕ) (k : ℕ) :
    (RetainedPathSearch.rounds (t := t) E a k).1=(RetainedPathSearch.rounds (t := t) E b k).1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [RetainedPathSearch.rounds,pass_state_independent a b,ih]

theorem extract_edges_congr {G : Digraph (Fin n)} [DecidableRel G.Adj] {t : Fin n}
    (S T : RetainedPathSearch.State G t)
    (hS : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys S.legacy.entries)
    (hT : ∀ u, SimplePath G u t → u ∈ ResidualSearch.keys T.legacy.entries)
    (s : Fin n) (h : S=T) :
    (RetainedPathSearch.extract S hS s).edges=(RetainedPathSearch.extract T hT s).edges := by
  cases h
  rfl

theorem search_edges_independent {G : Digraph (Fin n)} [DecidableRel G.Adj]
    (E : ResidualSearch.Enumeration (Fin n))
    (a b : (u v : Fin n) → Decidable (G.Adj u v) × ℕ) (s t : Fin n) :
    (RetainedPathSearch.search E a s t).edges=(RetainedPathSearch.search E b s t).edges := by
  unfold RetainedPathSearch.search
  dsimp only
  exact extract_edges_congr _ _ _ _ s (rounds_state_independent E a b _)

/-- The existing retained support search supplies edges; the recovery sum itself
executes binary fraction additions and retains their unreduced fields. -/
def recover (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (s t : Fin n) (es : List (Pair n)) : Candidate n × ℕ :=
  let r := RetainedPathSearch.search E (supportTest adjacency es) s t
  let values := costList cost r.edges
  let total := BinaryFractionalRows.sum values.1
  (⟨r.edges,total.1⟩,r.work+values.2+total.2+8)

theorem recover_decode (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (s t : Fin n) (es : List (Pair n)) :
    decode (recover E adjacency cost s t es).1 =
      (FractionalCoverRawOracle.recover E (graph adjacency) (decodeCost cost) s t es).1 := by
  have he := search_edges_independent E (supportTest adjacency es)
    (FractionalCoverPathOracle.supportTest (graph adjacency) es) s t
  simp [recover,FractionalCoverRawOracle.recover,decode,BinaryFractionalRows.sum_decode,costList_decode,he]

def shortest (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (s t : Fin n) : Option (Candidate n) × ℕ :=
  let r := minimize E adjacency cost s t
  match r.1 with
  | none => (none,r.2+4)
  | some q =>
    let p := recover E adjacency cost s t q.edges
    (some p.1,r.2+p.2+6)

/-- Exact raw refinement preserves absence, retained edge order, numerator and denominator. -/
theorem shortest_decode (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (s t : Fin n) :
    (shortest E adjacency cost s t).1.map decode =
      (FractionalCoverRawOracle.shortest E (graph adjacency) (decodeCost cost) s t).1 := by
  have h := minimize_decode E adjacency cost s t
  cases hr : (minimize E adjacency cost s t).1 with
  | none => simp only [shortest,FractionalCoverRawOracle.shortest,← h,hr,Option.map_none]
  | some q =>
    simp only [shortest,FractionalCoverRawOracle.shortest,← h,hr,Option.map_some]
    exact congrArg some (recover_decode E adjacency cost s t q.edges)

/-- Every returned edge list is an actual simple path with its exact cost. -/
theorem shortest_valid (E : ResidualSearch.Enumeration (Fin n)) (adjacency : Adjacency n)
    (cost : Cost n) (s t : Fin n) {q : Candidate n}
    (hq : (shortest E adjacency cost s t).1=some q) :
    FractionalCoverPathOracle.SimpleValid (graph adjacency)
      (fun e => FractionalCoverRawCore.rational (decodeCost cost e)) s t
      (FractionalCoverRawOracle.decode (decode q)) := by
  have hb := shortest_decode E adjacency cost s t
  rw [hq,Option.map_some] at hb
  have hr := congrArg Prod.fst (FractionalCoverRawOracle.shortest_refines E
    (graph adjacency) (decodeCost cost) s t)
  change ((FractionalCoverRawOracle.shortest E (graph adjacency) (decodeCost cost) s t).1.map
    FractionalCoverRawOracle.decode) = _ at hr
  rw [← hb,Option.map_some] at hr
  exact FractionalCoverPathOracle.shortest_valid E (graph adjacency) _ s t hr.symm

end DirectedFlowCutGap.BinaryFractionalWalkOracle
