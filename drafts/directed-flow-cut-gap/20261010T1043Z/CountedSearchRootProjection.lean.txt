import DirectedFlowCutGap.EncodedShortcutReachability

/-!
# Exact root-only projection of counted shortcut search

Shortcut construction observes only the found/stopped tag. The finite program
below retains the roots of the original search table in exactly the same order;
it never constructs or evaluates a SimplePath payload. Each theorem relates
this projection to the actual counted search body, including its intermediate
states. Thus omitting those payloads is justified by a proved observation law.

No bit-cost theorem is asserted here. The abstract Boolean tests must still be
instantiated with the closed binary equality and restricted-adjacency bodies;
their list control and representation movement must receive execution
certificates. This module cannot price an arbitrary supplied function.
-/
namespace DirectedFlowCutGap.CountedSearchRootProjection
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem scan_presence {α β : Type*} (P : α → Prop) (test : CountedSearch.Test P)
    (key : α → β) (p : β → Bool) (hp : ∀ x, P x ↔ p (key x)=true) (xs : List α) :
    (CountedSearch.scan P test xs).1.isSome = (xs.map key).any p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      unfold CountedSearch.scan
      dsimp only
      split
      · rename_i h he
        have hb := (hp x).mp h
        simp [List.any_cons,hb]
      · rename_i h he
        have hb : p (key x)=false := by
          cases hx : p (key x)
          · rfl
          · exact False.elim (h ((hp x).mpr hx))
        simpa only [Option.isSome_map,List.map_cons,List.any_cons,hb,Bool.false_or] using ih

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {t : V} [DecidableRel G.Adj]

def roots (S : ResidualSearch.State G t) : List V := S.entries.map Sigma.fst

/-- These two scans have the same short-circuit order as the two original
first-hit scans; only their found tags are required to choose the next state. -/
def visit (adj : V → V → Bool) (xs : List V) (v : V) : List V :=
  if xs.any (fun u => decide (u=v)) then xs
  else if xs.any (adj v) then v::xs else xs

omit [Fintype V] in
theorem visit_roots (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (S : ResidualSearch.State G t) (v : V) :
    roots (CountedSearch.visit test S v).1 =
      visit (fun u w => decide (G.Adj u w)) (roots S) v := by
  have he := scan_presence (fun e : ResidualSearch.Entry G t => e.1=v)
    (fun e => (inferInstanceAs (Decidable (e.1=v)),1)) Sigma.fst
    (fun u => decide (u=v)) (by intro e; simp) S.entries
  have ha := scan_presence (fun e : ResidualSearch.Entry G t => G.Adj v e.1)
    (fun e => test v e.1) Sigma.fst (fun u => decide (G.Adj v u))
    (by intro e; simp) S.entries
  unfold CountedSearch.visit
  dsimp only
  split
  · rename_i e hr
    rw [hr] at he
    simp only [Option.isSome_some] at he
    simp only [visit,roots,← he,ite_true]
  · rename_i hr
    rw [hr] at he
    simp only [Option.isSome_none] at he
    split
    · rename_i hq
      rw [hq] at ha
      simp only [Option.isSome_none] at ha
      simp only [visit,roots,← he,← ha,Bool.false_eq_true,ite_false]
    · rename_i e hq
      rw [hq] at ha
      simp only [Option.isSome_some] at ha
      simp only [visit,roots,← he,← ha,Bool.false_eq_true,ite_false,ite_true,
        ResidualSearch.State.add,List.map_cons]

def pass (adj : V → V → Bool) : List V → List V → List V
  | [],xs => xs
  | v::vs,xs => pass adj vs (visit adj xs v)

omit [Fintype V] in
theorem pass_roots (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (vs : List V) (S : ResidualSearch.State G t) :
    roots (CountedSearch.pass test vs S).1 =
      pass (fun u v => decide (G.Adj u v)) vs (roots S) := by
  induction vs generalizing S with
  | nil => rfl
  | cons v vs ih => simp only [CountedSearch.pass,pass,ih,visit_roots]

def rounds (adj : V → V → Bool) (vs : List V) (t : V) : ℕ → List V
  | 0 => [t]
  | k+1 => pass adj vs (rounds adj vs t k)

omit [Fintype V] in
theorem rounds_roots (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (k : ℕ) :
    roots (CountedSearch.rounds (t := t) E test k).1 =
      rounds (fun u v => decide (G.Adj u v)) E.vertices t k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [CountedSearch.rounds,rounds,pass_roots,ih]

omit [Fintype V] [DecidableRel G.Adj] in
theorem extract_found (S : ResidualSearch.State G t)
    (complete : ∀ u, SimplePath G u t → u∈ResidualSearch.keys S.entries) (s : V) :
    EncodedShortcutReachability.Input.found (CountedSearch.extract S complete s).1 =
      (roots S).any (fun u => decide (u=s)) := by
  have h := scan_presence (fun e : ResidualSearch.Entry G t => e.1=s)
    (fun e => (inferInstanceAs (Decidable (e.1=s)),1)) Sigma.fst
    (fun u => decide (u=s)) (by intro e; simp) S.entries
  unfold CountedSearch.extract
  dsimp only
  split
  · rename_i e hr
    rw [hr] at h
    exact h
  · rename_i hr
    rw [hr] at h
    exact h

def search (adj : V → V → Bool) (vs : List V) (s t : V) (fuel : ℕ) : Bool :=
  (rounds adj vs t fuel).any (fun u => decide (u=s))

theorem search_found (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (s t : V) :
    EncodedShortcutReachability.Input.found (CountedSearch.search E test s t).1 =
      search (fun u v => decide (G.Adj u v)) E.vertices s t (Fintype.card V) := by
  unfold CountedSearch.search
  dsimp only
  rw [extract_found,rounds_roots]
  rfl

/-- A single visit's reached root table inherits the original invariant. -/
theorem visit_length (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (S : ResidualSearch.State G t) (v : V) :
    (visit (fun u w => decide (G.Adj u w)) (roots S) v).length ≤ Fintype.card V := by
  rw [← visit_roots test S v]
  simpa only [roots,List.length_map] using (CountedSearch.visit test S v).1.length_le_card

/-- This holds for every passed prefix, not just a completed outer round. -/
theorem pass_length (test : (u v : V) → Decidable (G.Adj u v) × ℕ)
    (vs : List V) (S : ResidualSearch.State G t) :
    (pass (fun u v => decide (G.Adj u v)) vs (roots S)).length ≤ Fintype.card V := by
  rw [← pass_roots test vs S]
  simpa only [roots,List.length_map] using (CountedSearch.pass test vs S).1.length_le_card

/-- Round boundaries also inherit the original finite-cardinality invariant. -/
theorem rounds_length (E : ResidualSearch.Enumeration V)
    (test : (u v : V) → Decidable (G.Adj u v) × ℕ) (k : ℕ) :
    (rounds (fun u v => decide (G.Adj u v)) E.vertices t k).length ≤ Fintype.card V := by
  rw [← rounds_roots E test k]
  simpa only [roots,List.length_map] using
    (CountedSearch.rounds (t := t) E test k).1.length_le_card

end DirectedFlowCutGap.CountedSearchRootProjection
