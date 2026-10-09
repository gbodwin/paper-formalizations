import DirectedFlowCutGap.FractionalCoverRawCore
import DirectedFlowCutGap.FractionalCoverPathOracle

/-!
# Unreduced bounded-walk and retained path oracle

The runtime carries the same actual edge witnesses as the frozen rational
oracle, with natural-fraction costs and cross-product comparisons. The semantic
map to rational records appears only in refinement proofs. The inherited
counters remain partial rational-operation charges; binary arithmetic and the
complete list/loop cost model are separate obligations.
-/
namespace DirectedFlowCutGap.FractionalCoverRawOracle
open FractionalCoverRawCore RawNonnegativeRational IntegralNetworkFlow Tabulated
open FractionalCoverPathOracle
variable {V : Type*} [DecidableEq V]

structure Candidate (V : Type*) where
  edges : List (V × V)
  cost : Code

abbrev Table (V : Type*) := List (V × Candidate V)

def decode (p : Candidate V) : FractionalCoverWalkOracle.Candidate V := ⟨p.edges,rational p.cost⟩
def decodeTable (xs : Table V) : FractionalCoverWalkOracle.Table V :=
  xs.map (fun q => (q.1,decode q.2))
def decodeResult (r : Option (Candidate V) × ℕ) : Option (FractionalCoverWalkOracle.Candidate V) × ℕ :=
  (r.1.map decode,r.2)

def zero : Candidate V := ⟨[],Code.zero⟩
def extend (cost : V × V → Code) (u v : V) (q : Candidate V) : Candidate V :=
  ⟨(u,v)::q.edges,(cost (u,v)).add q.cost⟩

def pick : Option (Candidate V) → Option (Candidate V) → Option (Candidate V)
  | none,b => b
  | a,none => a
  | some a,some b => if a.cost.le b.cost then some a else some b

omit [DecidableEq V] in
@[simp] lemma decode_zero : decode (zero : Candidate V) = FractionalCoverWalkOracle.zero := by
  simp [decode,zero,FractionalCoverWalkOracle.zero]

omit [DecidableEq V] in
@[simp] lemma decode_extend (cost : V × V → Code) (u v : V) (q : Candidate V) :
    decode (extend cost u v q) =
      FractionalCoverWalkOracle.extend (fun e => rational (cost e)) u v (decode q) := by
  simp [decode,extend,FractionalCoverWalkOracle.extend]

omit [DecidableEq V] in
lemma pick_refines (a b : Option (Candidate V)) :
    (pick a b).map decode = FractionalCoverWalkOracle.pick (a.map decode) (b.map decode) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      by_cases h : a.cost.le b.cost = true
      · simp [pick,FractionalCoverWalkOracle.pick,h,decode,(code_le_iff _ _).mp h]
      · have hn : ¬rational a.cost ≤ rational b.cost := (code_le_iff _ _).not.mp h
        simp [pick,FractionalCoverWalkOracle.pick,h,decode,hn]

def scan (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code) (u : V) :
    Table V → Option (Candidate V) × ℕ
  | [] => (none,0)
  | (v,q)::xs =>
      let r := scan G cost u xs
      if G.Adj u v then (pick (some (extend cost u v q)) r.1,r.2+5)
      else (r.1,r.2+1)

def atVertex (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (t u : V) (old : Table V) : Option (Candidate V) × ℕ :=
  if u=t then (some zero,1) else
    let r := scan G cost u old
    (r.1,r.2+1)

def pass (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (t : V) (old : Table V) : List V → Table V × ℕ
  | [] => ([],0)
  | u::us =>
      let r := atVertex G cost t u old
      let tail := pass G cost t old us
      match r.1 with
      | none => (tail.1,r.2+tail.2+1)
      | some q => ((u,q)::tail.1,r.2+tail.2+2)

def rounds (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → Code) (t : V) : ℕ → Table V × ℕ
  | 0 => ([(t,zero)],1)
  | k+1 =>
    let old := rounds vs G cost t k
    let next := pass G cost t old.1 vs
    (next.1,old.2+next.2)

def lookup (u : V) : Table V → Option (Candidate V) × ℕ
  | [] => (none,0)
  | (v,q)::xs =>
    let tail := lookup u xs
    if u=v then (pick (some q) tail.1,tail.2+2) else (tail.1,tail.2+1)

def minimize (E : ResidualSearch.Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → Code) (s t : V) : Option (Candidate V) × ℕ :=
  let table := rounds E.vertices G cost t E.vertices.length
  let r := lookup s table.1
  (r.1,table.2+r.2)

omit [DecidableEq V] in
lemma scan_refines (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (u : V) (xs : Table V) : decodeResult (scan G cost u xs) =
      FractionalCoverWalkOracle.scan G (fun e => rational (cost e)) u (decodeTable xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨v,q⟩
    have h1 := congrArg Prod.fst ih
    have h2 := congrArg Prod.snd ih
    dsimp only [decodeResult,decodeTable] at h1 h2
    by_cases ha : G.Adj u v <;>
      simp [scan,FractionalCoverWalkOracle.scan,decodeResult,decodeTable,ha,
        pick_refines,← h1,← h2]

lemma atVertex_refines (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (t u : V) (old : Table V) : decodeResult (atVertex G cost t u old) =
      FractionalCoverWalkOracle.atVertex G (fun e => rational (cost e)) t u (decodeTable old) := by
  have h := scan_refines G cost u old
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  by_cases he : u=t <;>
    simp [atVertex,FractionalCoverWalkOracle.atVertex,he,decodeResult,← h1,← h2]

lemma pass_refines (G : Digraph V) [DecidableRel G.Adj] (cost : V × V → Code)
    (t : V) (old : Table V) (vs : List V) :
    (decodeTable (pass G cost t old vs).1,(pass G cost t old vs).2) =
      FractionalCoverWalkOracle.pass G (fun e => rational (cost e)) t (decodeTable old) vs := by
  induction vs with
  | nil => rfl
  | cons u us ih =>
    have h := atVertex_refines G cost t u old
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have ht1 := congrArg Prod.fst ih
    have ht2 := congrArg Prod.snd ih
    dsimp only [decodeResult,decodeTable] at h1 h2 ht1 ht2
    cases hr : (atVertex G cost t u old).1 <;>
      simp [pass,FractionalCoverWalkOracle.pass,← h1,← h2,← ht1,← ht2,hr,decodeTable]

lemma rounds_refines (vs : List V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → Code) (t : V) (k : ℕ) :
    (decodeTable (rounds vs G cost t k).1,(rounds vs G cost t k).2) =
      FractionalCoverWalkOracle.rounds vs G (fun e => rational (cost e)) t k := by
  induction k with
  | zero => simp [rounds,FractionalCoverWalkOracle.rounds,decodeTable]
  | succ k ih =>
    have h := pass_refines G cost t (rounds vs G cost t k).1 vs
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hi1 := congrArg Prod.fst ih
    have hi2 := congrArg Prod.snd ih
    simp only [rounds,FractionalCoverWalkOracle.rounds,← hi1,← hi2,← h1,← h2]

lemma lookup_refines (u : V) (xs : Table V) : decodeResult (lookup u xs) =
    FractionalCoverWalkOracle.lookup u (decodeTable xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨v,q⟩
    have h1 := congrArg Prod.fst ih
    have h2 := congrArg Prod.snd ih
    dsimp only [decodeResult,decodeTable] at h1 h2
    by_cases he : u=v
    · subst v
      simp [lookup,FractionalCoverWalkOracle.lookup,decodeResult,decodeTable,
        pick_refines,← h1,← h2]
    · simp [lookup,FractionalCoverWalkOracle.lookup,decodeResult,decodeTable,he,← h1,← h2]

theorem minimize_refines (E : ResidualSearch.Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → Code) (s t : V) : decodeResult (minimize E G cost s t) =
    FractionalCoverWalkOracle.minimize E G (fun e => rational (cost e)) s t := by
  have hr := rounds_refines E.vertices G cost t E.vertices.length
  have hl := lookup_refines s (rounds E.vertices G cost t E.vertices.length).1
  have hr1 := congrArg Prod.fst hr
  have hr2 := congrArg Prod.snd hr
  have hl1 := congrArg Prod.fst hl
  have hl2 := congrArg Prod.snd hl
  simp only [minimize,FractionalCoverWalkOracle.minimize,decodeResult,← hr1,← hr2,← hl1,← hl2]

variable [Fintype V]

/-- Only retained edges are read. The raw sum uses no rational arithmetic. -/
def recover (E : ResidualSearch.Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → Code) (s t : V) (es : List (V × V)) : Candidate V × ℕ :=
  let r := RetainedPathSearch.search E (supportTest G es) s t
  (⟨r.edges,sumCodes (r.edges.map cost)⟩,r.work+3*r.edges.length+1)

lemma recover_refines (E : ResidualSearch.Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → Code) (s t : V) (es : List (V × V))
    (hw : FractionalCoverWalkOracle.IsWalk G s es t) :
    (decode (recover E G cost s t es).1,(recover E G cost s t es).2) =
      FractionalCoverPathOracle.recover E G (fun e => rational (cost e)) s t es hw := by
  unfold recover FractionalCoverPathOracle.recover
  dsimp only
  split
  · simp [decode,List.map_map,Function.comp_def]
  · rename_i hn _
    exact False.elim (hn (support_has_path hw))

def shortest (E : ResidualSearch.Enumeration V) (G : Digraph V) [DecidableRel G.Adj]
    (cost : V × V → Code) (s t : V) : Option (Candidate V) × ℕ :=
  let r := minimize E G cost s t
  match r.1 with
  | none => (none,r.2+1)
  | some q =>
    let p := recover E G cost s t q.edges
    (some p.1,r.2+p.2+1)

theorem shortest_refines (E : ResidualSearch.Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → Code) (s t : V) :
    decodeResult (shortest E G cost s t) =
      FractionalCoverPathOracle.shortest E G (fun e => rational (cost e)) s t := by
  have h := minimize_refines E G cost s t
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only [decodeResult] at h1 h2
  cases hr : (minimize E G cost s t).1 with
  | none =>
    have hnone : (FractionalCoverWalkOracle.minimize E G (fun e => rational (cost e)) s t).1=none :=
      h1.symm.trans (by simp [hr])
    simp only [shortest,hr,decodeResult,Option.map_none]
    unfold FractionalCoverPathOracle.shortest
    dsimp only
    split
    · simp only [h2]
    · rename_i r hbad
      rw [hnone] at hbad
      cases hbad
  | some q =>
    have hsome : (FractionalCoverWalkOracle.minimize E G (fun e => rational (cost e)) s t).1=some (decode q) :=
      h1.symm.trans (by simp [hr])
    have hw := (FractionalCoverWalkOracle.minimize_valid E G (fun e => rational (cost e)) s t hsome).1
    have hrp := recover_refines E G cost s t q.edges hw
    have hp1 := congrArg Prod.fst hrp
    have hp2 := congrArg Prod.snd hrp
    simp only [shortest,hr,decodeResult,Option.map_some]
    unfold FractionalCoverPathOracle.shortest
    dsimp only
    split
    · rename_i hbad
      rw [hsome] at hbad
      cases hbad
    · rename_i r hr'
      have heq : r=decode q := Option.some.inj (hr'.symm.trans hsome)
      subst r
      dsimp only [decode] at hp1 hp2 ⊢
      rw [← hp1,← hp2,← h2]

/-- Exact transfer of the explicitly partial frozen operation charge. -/
theorem shortest_charge_le (E : ResidualSearch.Enumeration V) (G : Digraph V)
    [DecidableRel G.Adj] (cost : V × V → Code) (s t : V) :
    (shortest E G cost s t).2 ≤ FractionalCoverPathOracle.shortestCharge (Fintype.card V) := by
  have he := congrArg Prod.snd (shortest_refines E G cost s t)
  change (shortest E G cost s t).2 = _ at he
  rw [he]
  exact FractionalCoverPathOracle.shortest_charge_le E G (fun e => rational (cost e)) s t

end DirectedFlowCutGap.FractionalCoverRawOracle
