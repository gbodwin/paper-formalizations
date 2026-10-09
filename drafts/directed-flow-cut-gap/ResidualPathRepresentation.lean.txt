import DirectedFlowCutGap.TabulatedIntegralFlow

/-!
# Operational provenance of the finite search's path coordinates

An arbitrary function-valued path need not have cheap coordinate access. The
frozen finite search, however, builds paths only from `refl` and `prepend`.
`Generated` records that exact representation. `CoordinateSteps` gives the
number of `Fin.cases`/base-return instructions for that representation and is
proved both value-correct and bounded on every path the search can return.
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow
namespace PathRepresentation

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {s t : V}

inductive Generated : {s t : V} → SimplePath G s t → Prop
  | refl (s : V) : Generated (SimplePath.refl G s)
  | prepend {s u t : V} (p : SimplePath G u t) (h : G.Adj s u)
      (hs : s ∉ p.vertices) (hp : Generated p) : Generated (p.prepend h hs)

omit [Fintype V] in
theorem Generated.cast_source {u v t : V} {p : SimplePath G u t}
    (hp : Generated p) (h : u=v) : Generated (h ▸ p) := by
  subst v
  exact hp

/-- A step means a coordinate-code case or the zero-path's return. Proof fields
and adjacency certificates are erased and are not runtime instructions. -/
inductive CoordinateSteps : {s t : V} → (p : SimplePath G s t) →
    Fin (p.edgeLength+1) → V → ℕ → Prop
  | refl (s : V) : CoordinateSteps (SimplePath.refl G s) 0 s 1
  | head {s u t : V} (p : SimplePath G u t) (h : G.Adj s u) (hs : s ∉ p.vertices) :
      CoordinateSteps (p.prepend h hs) 0 s 1
  | tail {s u t : V} (p : SimplePath G u t) (h : G.Adj s u) (hs : s ∉ p.vertices)
      (i : Fin (p.edgeLength+1)) (v : V) (k : ℕ) (eval : CoordinateSteps p i v k) :
      CoordinateSteps (p.prepend h hs) i.succ v (k+1)

omit [Fintype V] in
theorem coordinateSteps_value {p : SimplePath G s t} {i : Fin (p.edgeLength+1)}
    {v : V} {k : ℕ} (h : CoordinateSteps p i v k) : p.vertex i = v := by
  induction h with
  | refl => rfl
  | head => rfl
  | tail p h hs i v k he ih => simpa only [SimplePath.prepend, Fin.cases_succ] using ih

omit [Fintype V] in
theorem generated_coordinateSteps {p : SimplePath G s t} (hp : Generated p)
    (i : Fin (p.edgeLength+1)) : CoordinateSteps p i (p.vertex i) (i.val+1) := by
  induction hp with
  | refl s =>
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact CoordinateSteps.refl s
  | @prepend s u t p h hs hp ih =>
    cases i using Fin.cases with
    | zero => exact CoordinateSteps.head p h hs
    | succ i =>
      change CoordinateSteps (p.prepend h hs) i.succ (p.vertex i) ((i.val+1)+1)
      exact CoordinateSteps.tail p h hs i (p.vertex i) (i.val+1) (ih i)

theorem generated_access_le {p : SimplePath G s t} (hp : Generated p)
    (i : Fin (p.edgeLength+1)) :
    ∃ k ≤ Fintype.card V, CoordinateSteps p i (p.vertex i) k := by
  refine ⟨i.val+1, ?_, generated_coordinateSteps hp i⟩
  have hl := p.edgeLength_lt_card
  have hi := i.isLt
  omega

def StateGenerated (S : ResidualSearch.State G t) : Prop :=
  ∀ e ∈ S.entries, Generated e.2

omit [Fintype V] in
theorem initial_generated (G : Digraph V) (t : V) :
    StateGenerated (ResidualSearch.State.initial G t) := by
  intro e he
  simp only [ResidualSearch.State.initial, List.mem_singleton] at he
  subst e
  exact Generated.refl t

omit [Fintype V] in
theorem add_generated (S : ResidualSearch.State G t) (hS : StateGenerated S)
    (v : V) (hv : v ∉ ResidualSearch.keys S.entries)
    (e : ResidualSearch.Entry G t) (he : e ∈ S.entries) (ha : G.Adj v e.1) :
    StateGenerated (S.add v hv e he ha) := by
  intro q hq
  change q ∈ _ :: S.entries at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact Generated.prepend e.2 ha (fun h => hv (S.support e he h)) (hS e he)
  · exact hS q hq

variable [DecidableRel G.Adj]

omit [Fintype V] in
theorem visit_generated (S : ResidualSearch.State G t) (hS : StateGenerated S) (v : V) :
    StateGenerated (ResidualSearch.visit S v).1 := by
  unfold ResidualSearch.visit
  dsimp only
  split
  · exact hS
  · rename_i hn
    split
    · exact hS
    · rename_i e heq
      have hv : v ∉ ResidualSearch.keys S.entries := by
        intro h
        obtain ⟨a,ha,hav⟩ := ResidualSearch.mem_keys.mp h
        exact ResidualSearch.scan_none _ _ hn a ha hav
      exact add_generated S hS v hv e.1 e.2.1 e.2.2

omit [Fintype V] in
theorem pass_generated (vs : List V) (S : ResidualSearch.State G t)
    (hS : StateGenerated S) : StateGenerated (ResidualSearch.pass vs S).1 := by
  induction vs generalizing S with
  | nil => exact hS
  | cons v vs ih => exact ih _ (visit_generated S hS v)

omit [Fintype V] in
theorem rounds_generated (vs : List V) (k : ℕ) :
    StateGenerated (ResidualSearch.rounds vs G t k).1 := by
  induction k with
  | zero => exact initial_generated G t
  | succ k ih => exact pass_generated vs _ ih

def ResultGenerated (r : ResidualSearch.Result G s t) : Prop :=
  match r with
  | .found p => Generated p
  | .stopped _ => True

/-- This is about the precise function-valued paths returned by the frozen
search, not a cheaper path having the same mathematical endpoints. -/
theorem search_generated (E : ResidualSearch.Enumeration V) (s t : V) :
    match (ResidualSearch.search E G s t).1 with
    | .found p => Generated p
    | .stopped _ => True := by
  change ResultGenerated (ResidualSearch.search E G s t).1
  unfold ResidualSearch.search
  dsimp only
  split
  · rename_i e he
    have hp := rounds_generated (G := G) (t := t) E.vertices (Fintype.card V)
      e.1 e.2.1
    exact hp.cast_source e.2.2
  · trivial

/-- The sum charges both endpoint coordinate programs and two output cells
per edge. Evaluation is justified only under the proved `Generated` invariant. -/
def edgeMaterializationCharge {s t : V} (p : SimplePath G s t) : ℕ :=
  ∑ i : Fin p.edgeLength, ((i.val+1)+(i.val+2)+2)

omit [DecidableRel G.Adj] in
theorem edgeMaterializationCharge_bound {s t : V} (p : SimplePath G s t) :
    edgeMaterializationCharge p ≤ Fintype.card V * (2*Fintype.card V+3) := by
  have hl := p.edgeLength_lt_card
  calc
    _ ≤ ∑ _i : Fin p.edgeLength, (2*Fintype.card V+3) := by
      unfold edgeMaterializationCharge
      apply Finset.sum_le_sum
      intro i _
      have hi := i.isLt
      omega
    _ = p.edgeLength*(2*Fintype.card V+3) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_of_lt hl)

end PathRepresentation
end DirectedFlowCutGap.IntegralNetworkFlow
