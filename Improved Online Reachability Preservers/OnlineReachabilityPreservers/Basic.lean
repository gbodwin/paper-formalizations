import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! Finite directed graphs and a bounded reachability computation. -/

namespace OnlineReachabilityPreservers

open Finset Relation

abbrev Arcs (V : Type*) := Finset (V × V)

variable {V : Type*}

def Edge (G : Arcs V) (u v : V) : Prop := (u, v) ∈ G

instance [DecidableEq V] (G : Arcs V) : DecidableRel (Edge G) := fun _ _ => inferInstanceAs (Decidable (_ ∈ G))

/-- Reachability includes a walk of length zero. -/
abbrev Reach (G : Arcs V) : V → V → Prop := ReflTransGen (Edge G)

theorem reach_mono {G H : Arcs V} (sub : H ⊆ G) {u v : V} (h : Reach H u v) :
    Reach G u v := by
  induction h with
  | refl => exact .refl
  | tail _ hv ih => exact ih.tail (sub hv)

def IsDAG (G : Arcs V) : Prop := ∀ ⦃u v⦄, Edge G u v → ¬ Reach G v u

/-- An explicit ordered edge list with the indicated endpoints. -/
inductive Walk (G : Arcs V) : V → V → List (V × V) → Prop
  | nil (v : V) : Walk G v v []
  | cons {u v t : V} {rest : List (V × V)} (edge : Edge G u v) (tail : Walk G v t rest) :
      Walk G u t ((u, v) :: rest)

namespace Walk

variable {G : Arcs V} {s t : V} {path : List (V × V)}

theorem mono {H : Arcs V} (walk : Walk H s t path) (sub : H ⊆ G) :
    Walk G s t path := by
  induction walk with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (sub h) ih

theorem append {u : V} {q : List (V × V)} (w : Walk G s t path) (z : Walk G t u q) :
    Walk G s u (path ++ q) := by
  induction w with
  | nil => exact z
  | cons h _ ih => exact .cons h (ih z)

theorem vertex_list (walk : Walk G s t path) :
    s :: path.map Prod.snd = path.map Prod.fst ++ [t] := by
  induction walk with
  | nil => rfl
  | cons h w ih =>
    simpa only [List.map_cons, List.cons_append, List.cons.injEq, true_and] using ih

theorem reachable (walk : Walk G s t path) : Reach G s t := by
  induction walk with
  | nil => exact .refl
  | cons he _ ih => exact ih.head he

theorem mem (walk : Walk G s t path) {e : V × V} (he : e ∈ path) : e ∈ G := by
  induction walk with
  | nil => simp at he
  | cons he' _ ih =>
    rcases List.mem_cons.mp he with h | h
    · exact h ▸ he'
    · exact ih h

theorem in_edges [DecidableEq V] (walk : Walk G s t path) : Walk path.toFinset s t path := by
  have lift {H : Arcs V} (sub : ∀ e ∈ path, e ∈ H) : Walk H s t path := by
    induction walk with
    | nil => exact nil _
    | cons _ _ ih => exact cons (sub _ (by simp)) (ih (by aesop))
  exact lift (by simp)

theorem from_start (walk : Walk G s t path) {e : V × V} (he : e ∈ path) :
    Reach G s e.1 := by
  induction walk with
  | nil => simp at he
  | cons he' _ ih =>
    rcases List.mem_cons.mp he with rfl | h
    · exact .refl
    · exact (ih h).head he'

theorem to_end (walk : Walk G s t path) {e : V × V} (he : e ∈ path) :
    Reach G e.2 t := by
  induction walk with
  | nil => simp at he
  | cons _ next ih =>
    rcases List.mem_cons.mp he with rfl | h
    · exact next.reachable
    · exact ih h

/-- Two different edges of one walk are ordered by a connector in that walk. -/
theorem edge_order (walk : Walk G s t path) {e f : V × V}
    (he : e ∈ path) (hf : f ∈ path) (hne : e ≠ f) :
    Reach G e.2 f.1 ∨ Reach G f.2 e.1 := by
  induction walk with
  | nil => simp at he
  | cons _ next ih =>
    rcases List.mem_cons.mp he with eh | et <;> rcases List.mem_cons.mp hf with fh | ft
    · exact (hne (eh.trans fh.symm)).elim
    · exact Or.inl (eh ▸ next.from_start ft)
    · exact Or.inr (fh ▸ next.from_start et)
    · exact ih et ft

end Walk

section FiniteSearch

variable [DecidableEq V]

/-- Vertices that reach the target in at most the given number of edges. -/
def reachIn (G : Arcs V) (t : V) : ℕ → Finset V
  | 0 => {t}
  | k + 1 =>
    let prev := reachIn G t k
    prev ∪ (G.filter fun e => e.2 ∈ prev).image Prod.fst

theorem reachIn_succ {G : Arcs V} {t u : V} {k : ℕ} :
    u ∈ reachIn G t (k + 1) ↔
      u ∈ reachIn G t k ∨ ∃ v, Edge G u v ∧ v ∈ reachIn G t k := by
  simp only [reachIn, mem_union, mem_image, mem_filter, Prod.exists, Edge]
  grind

theorem reachIn_subset_succ (G : Arcs V) (t : V) (k : ℕ) :
    reachIn G t k ⊆ reachIn G t (k + 1) := fun _ h => reachIn_succ.mpr (Or.inl h)

theorem target_mem_reachIn (G : Arcs V) (t : V) (k : ℕ) : t ∈ reachIn G t k := by
  induction k with
  | zero => simp [reachIn]
  | succ k ih => exact reachIn_subset_succ G t k ih

theorem reachIn_sound {G : Arcs V} {t u : V} {k : ℕ} (h : u ∈ reachIn G t k) :
    Reach G u t := by
  induction k generalizing u with
  | zero =>
    have hu : u = t := by simpa [reachIn] using h
    subst u
    exact .refl
  | succ k ih =>
    rcases reachIn_succ.mp h with h | ⟨v, huv, hv⟩
    · exact ih h
    · exact (ih hv).head huv

private theorem reachIn_grows_or_stable (G : Arcs V) (t : V) (k : ℕ) :
    reachIn G t k = reachIn G t (k + 1) ∨ k + 1 ≤ (reachIn G t k).card := by
  induction k with
  | zero => exact Or.inr (by simp [reachIn])
  | succ k ih =>
    rcases ih with h | h
    · left
      change reachIn G t (k + 1) =
        reachIn G t (k + 1) ∪
          (G.filter fun e => e.2 ∈ reachIn G t (k + 1)).image Prod.fst
      rw [← h]
      exact h
    · by_cases heq : reachIn G t (k + 1) = reachIn G t (k + 2)
      · exact Or.inl heq
      · right
        have hne : reachIn G t k ≠ reachIn G t (k + 1) := by
          intro hz
          apply heq
          change reachIn G t (k + 1) =
            reachIn G t (k + 1) ∪
              (G.filter fun e => e.2 ∈ reachIn G t (k + 1)).image Prod.fst
          rw [← hz]
          exact hz
        have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨reachIn_subset_succ G t k, hne⟩)
        omega

variable [Fintype V]

/-- The reverse search stabilizes by the number of vertices. -/
theorem reachIn_stable (G : Arcs V) (t : V) :
    reachIn G t (Fintype.card V) = reachIn G t (Fintype.card V + 1) := by
  rcases reachIn_grows_or_stable G t (Fintype.card V) with h | h
  · exact h
  · have := card_le_univ (s := reachIn G t (Fintype.card V))
    omega

def reaches (G : Arcs V) (t : V) : Finset V := reachIn G t (Fintype.card V)

@[simp]
theorem mem_reaches {G : Arcs V} {s t : V} : s ∈ reaches G t ↔ Reach G s t := by
  refine ⟨reachIn_sound, fun h => ?_⟩
  induction h using ReflTransGen.head_induction_on with
  | refl => exact target_mem_reachIn G t _
  | head edge _ ih =>
    unfold reaches at ih ⊢
    rw [reachIn_stable G t]
    exact reachIn_succ.mpr (Or.inr ⟨_, edge, ih⟩)

theorem reaches_card_lt {G : Arcs V} (dag : IsDAG G) {u v : V} (edge : Edge G u v) :
    (reaches G u).card < (reaches G v).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    exact mem_reaches.mpr ((mem_reaches.mp hx).tail edge)
  · intro h
    have hv : v ∈ reaches G v := mem_reaches.mpr .refl
    rw [← h] at hv
    exact dag edge (mem_reaches.mp hv)

end FiniteSearch

variable [DecidableEq V]

def reverseArcs (G : Arcs V) : Arcs V := G.image Prod.swap

@[simp]
theorem edge_reverseArcs {G : Arcs V} {u v : V} :
    Edge (reverseArcs G) u v ↔ Edge G v u := by
  simp [Edge, reverseArcs, Prod.swap_eq_iff_eq_swap]

theorem reach_reverseArcs {G : Arcs V} {u v : V} :
    Reach (reverseArcs G) u v ↔ Reach G v u := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ edge ih => exact ih.head (edge_reverseArcs.mp edge)
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ edge ih => exact ih.head (edge_reverseArcs.mpr edge)

theorem reverseArcs_dag {G : Arcs V} (dag : IsDAG G) : IsDAG (reverseArcs G) :=
  fun {_ _} edge reach => dag (edge_reverseArcs.mp edge) (reach_reverseArcs.mp reach)

@[simp]
theorem reverseArcs_card (G : Arcs V) : (reverseArcs G).card = G.card :=
  card_image_of_injective _ Prod.swap_injective

@[simp]
theorem reverseArcs_reverseArcs (G : Arcs V) : reverseArcs (reverseArcs G) = G := by
  ext ⟨u, v⟩
  exact edge_reverseArcs.trans edge_reverseArcs

theorem reverseArcs_mono {G H : Arcs V} (sub : H ⊆ G) :
    reverseArcs H ⊆ reverseArcs G := image_subset_image sub

theorem Walk.reverse {G : Arcs V} {s t : V} {path : List (V × V)}
    (walk : Walk G s t path) : Walk (reverseArcs G) t s (path.reverse.map Prod.swap) := by
  induction walk with
  | nil => exact .nil _
  | cons he _ ih =>
    rw [List.reverse_cons, List.map_append]
    exact ih.append (.cons (edge_reverseArcs.mpr he) (.nil _))

end OnlineReachabilityPreservers
