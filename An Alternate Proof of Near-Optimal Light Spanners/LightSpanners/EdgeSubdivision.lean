import LightSpanners.Distance
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! One-edge subdivision on `Option V`: `none` is the inserted vertex, and
`some` embeds every old vertex. The two replacement weights may be zero. -/
namespace LightSpanners
open SimpleGraph
variable {V : Type*}
attribute [local instance] Classical.propDecidable

def subdivideEdge (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | some x, none => x = u ∨ x = v
    | none, some y => y = u ∨ y = v
    | some x, some y => G.Adj x y ∧ s(x,y) ≠ s(u,v)
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact h.1.ne rfl⟩

theorem subdivision_adj_old {G : SimpleGraph V} {u v x y : V}
    (h : G.Adj x y) (hne : s(x,y) ≠ s(u,v)) :
    (subdivideEdge G u v).Adj (some x) (some y) := ⟨h, hne⟩

theorem subdivision_adj_new_left (G : SimpleGraph V) (u v : V) :
    (subdivideEdge G u v).Adj (some u) none := Or.inl rfl

theorem subdivision_adj_new_right (G : SimpleGraph V) (u v : V) :
    (subdivideEdge G u v).Adj (some v) none := Or.inr rfl

noncomputable def subdivideWeight (w : Sym2 V → ℝ) (u : V) (α β : ℝ) :
    Sym2 (Option V) → ℝ := by
  classical
  exact Sym2.lift ⟨fun x y => match x, y with
    | none, none => 0
    | some x, none => if x = u then α else β
    | none, some y => if y = u then α else β
    | some x, some y => w s(x,y), by
      intro x y
      cases x <;> cases y <;> simp [Sym2.eq_swap]⟩

@[simp] theorem subdivideWeight_old (w : Sym2 V → ℝ) (u x y : V) (α β : ℝ) :
    subdivideWeight w u α β s(some x, some y) = w s(x,y) := rfl

@[simp] theorem subdivideWeight_new (w : Sym2 V → ℝ) (u x : V) (α β : ℝ) :
    subdivideWeight w u α β s(none, some x) = (if x = u then α else β) := by
  classical
  rfl

@[simp] theorem subdivideWeight_new' (w : Sym2 V → ℝ) (u x : V) (α β : ℝ) :
    subdivideWeight w u α β s(some x, none) = (if x = u then α else β) := by
  classical
  rfl

/-- Every original walk lifts, replacing a traversal of the selected edge by
the two-edge path through the new vertex, with precisely the same weight. -/
theorem exists_subdivision_lift {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v)) {x y : V} (p : G.Walk x y) :
    ∃ q : (subdivideEdge G u v).Walk (some x) (some y),
      walkWeight (subdivideWeight w u α β) q = walkWeight w p := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons x z y hxz p ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases he : s(x,z) = s(u,v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨.cons (subdivision_adj_new_left G x z)
          (.cons (subdivision_adj_new_right G x z).symm q), ?_⟩
        simp only [walkWeight_cons, subdivideWeight_new, subdivideWeight_new',
          ite_true, ite_eq_right (by simpa using huv.ne.symm), hq]
        linarith
      · refine ⟨.cons (subdivision_adj_new_right G z x)
          (.cons (subdivision_adj_new_left G z x).symm q), ?_⟩
        simp only [walkWeight_cons, subdivideWeight_new, subdivideWeight_new',
          ite_true, ite_eq_right (by simpa using huv.ne.symm), hq]
        rw [Sym2.eq_swap] at hsum
        linarith
    · exact ⟨.cons (subdivision_adj_old hxz he) q, by simp [hq]⟩

theorem subdivideWeight_nonneg (w : Sym2 V → ℝ) (u : V) {α β : ℝ}
    (hw : ∀ e, 0 ≤ w e) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∀ e, 0 ≤ subdivideWeight w u α β e := by
  classical
  intro e
  induction e using Sym2.inductionOn with
  | hf x y =>
    cases x <;> cases y
    · exact le_rfl
    · simp only [subdivideWeight_new]; split_ifs <;> assumption
    · simp only [subdivideWeight_new']; split_ifs <;> assumption
    · exact hw _

/-- Distance in the subdivided graph is no greater on original vertices.
This direction does not need nonnegativity or finiteness. -/
theorem subdivision_distance_le {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v)) (x y : V) :
    weightedDistance (subdivideEdge G u v) (subdivideWeight w u α β)
      (some x) (some y) ≤ weightedDistance G w x y := by
  unfold weightedDistance
  apply le_iInf
  intro p
  obtain ⟨q, hq⟩ := exists_subdivision_lift huv w hsum p
  exact hq ▸ iInf_le _ q

/-- Contract a subdivided walk between original vertices. Excursions from an
endpoint to the inserted vertex and straight back may be discarded; their
weights are nonnegative, so contraction cannot increase total weight. -/
theorem exists_subdivision_contraction {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v)) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    {x y : V} (p : (subdivideEdge G u v).Walk (some x) (some y)) :
    ∃ q : G.Walk x y, walkWeight w q ≤ walkWeight (subdivideWeight w u α β) p := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases p with
    | nil => exact ⟨.nil, by simp⟩
    | @cons _ z _ hxz p =>
      cases z with
      | some z =>
        obtain ⟨q, hq⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p rfl
        exact ⟨.cons hxz.1 q, by simpa using add_le_add_left hq (w s(x,z))⟩
      | none =>
        cases p with
        | @cons _ z _ hnz p =>
          cases z with
          | none => exact hnz.elim
          | some z =>
            obtain ⟨q, hq⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p rfl
            have hx : x = u ∨ x = v := hxz
            have hz : z = u ∨ z = v := hnz
            rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
            · refine ⟨q, ?_⟩
              simp only [walkWeight_cons, subdivideWeight_new, subdivideWeight_new', ite_true]
              linarith
            · refine ⟨.cons huv q, ?_⟩
              simp only [walkWeight_cons, subdivideWeight_new, subdivideWeight_new',
                ite_true, ite_eq_right (by simpa using huv.ne.symm)]
              linarith
            · refine ⟨.cons huv.symm q, ?_⟩
              simp only [walkWeight_cons, subdivideWeight_new, subdivideWeight_new',
                ite_true, ite_eq_right (by simpa using huv.ne.symm)]
              rw [Sym2.eq_swap]
              linarith
            · refine ⟨q, ?_⟩
              simp only [walkWeight_cons, subdivideWeight_new, subdivideWeight_new',
                ite_eq_right (by simpa using huv.ne.symm)]
              linarith

/-- One-edge subdivision preserves weighted distance between all original
vertices, including disconnected pairs and zero replacement weights. -/
theorem subdivision_distance_eq {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v)) (hα : 0 ≤ α) (hβ : 0 ≤ β) (x y : V) :
    weightedDistance (subdivideEdge G u v) (subdivideWeight w u α β)
      (some x) (some y) = weightedDistance G w x y := by
  apply le_antisymm (subdivision_distance_le huv w hsum x y)
  unfold weightedDistance
  apply le_iInf
  intro p
  obtain ⟨q, hq⟩ := exists_subdivision_contraction huv w hsum hα hβ p
  exact (iInf_le _ q).trans (ENNReal.ofReal_le_ofReal hq)

/-- Connectedness is preserved by the explicit subdivision graph. -/
theorem subdivideEdge_connected {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (hG : G.Connected) : (subdivideEdge G u v).Connected := by
  have hr : ∀ x y : V, (subdivideEdge G u v).Reachable (some x) (some y) := by
    intro x y
    obtain ⟨p⟩ := hG x y
    obtain ⟨q, _⟩ := exists_subdivision_lift huv (fun _ => 0)
      (α := 0) (β := 0) (by norm_num) p
    exact q.reachable
  refine ⟨fun x y => ?_⟩
  cases x with
  | none =>
    cases y with
    | none => exact .rfl
    | some y => exact (subdivision_adj_new_left G u v).symm.reachable.trans (hr u y)
  | some x =>
    cases y with
    | none => exact (hr x u).trans (subdivision_adj_new_left G u v).reachable
    | some y => exact hr x y

theorem subdivideWeight_positive_edges {G : SimpleGraph V} {u v : V}
    (w : Sym2 V → ℝ) {α β : ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hα : 0 < α) (hβ : 0 < β) :
    ∀ e ∈ (subdivideEdge G u v).edgeSet, 0 < subdivideWeight w u α β e := by
  classical
  intro e
  induction e using Sym2.inductionOn with
  | hf x y =>
    intro he
    have hxy := (mem_edgeSet _).mp he
    cases x <;> cases y
    · exact hxy.elim
    · simp only [subdivideWeight_new]; split_ifs <;> assumption
    · simp only [subdivideWeight_new']; split_ifs <;> assumption
    · exact hw _ ((mem_edgeSet _).mpr hxy.1)

end LightSpanners
