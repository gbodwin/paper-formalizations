import MinorFreeSpanners.MinorSingletonDegree
import LightSpanners.EdgeSubdivision

/-! Minor reflection for the actual one-edge subdivision used by the
light-spanner normalization. The degree-two inserted vertex cannot be a
singleton branch for a clique of order at least four. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {V : Type*}

/-- Contract a walk through the degree-two subdivision vertex, retaining
only old vertices and never leaving the old part of its support set. -/
theorem contract_subdivision_walk {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (S : Set (Option V)) {x y : V}
    (p : (subdivideEdge G u v).Walk (some x) (some y))
    (hS : ∀ z ∈ p.support, z ∈ S) :
    ∃ q : G.Walk x y, ∀ z ∈ q.support, some z ∈ S := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    cases p with
    | nil =>
      exact ⟨.nil, by intro z hz; simpa using hS (some z) (by simpa using hz)⟩
    | @cons _ z _ hxz p =>
      cases z with
      | some z =>
        obtain ⟨q,hq⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega)
          p (fun z hz => hS z (by simp [hz])) rfl
        refine ⟨.cons hxz.1 q, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hS _ (by simp)
        · exact hq z hz
      | none =>
        cases p with
        | @cons _ z _ hnz p =>
          cases z with
          | none => exact hnz.elim
          | some z =>
            obtain ⟨q,hq⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega)
              p (fun z hz => hS z (by simp [hz])) rfl
            have hx : x = u ∨ x = v := hxz
            have hz : z = u ∨ z = v := hnz
            rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
            · exact ⟨q,hq⟩
            · refine ⟨.cons huv q, ?_⟩
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hS _ (by simp)
              · exact hq z hz
            · refine ⟨.cons huv.symm q, ?_⟩
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hS _ (by simp)
              · exact hq z hz
            · exact ⟨q,hq⟩

/-- If a branch contains the inserted vertex and any old vertex, its
internal walk supplies an old endpoint of the subdivided edge in that branch. -/
theorem subdivision_branch_endpoint {I : Type*} {F : SimpleGraph I}
    {G : SimpleGraph V} {u v : V} (M : MinorModel F (subdivideEdge G u v))
    (i : I) (hi : none ∈ M.branch i) (hold : ∃ x, some x ∈ M.branch i) :
    ∃ x, some x ∈ M.branch i ∧ (x = u ∨ x = v) := by
  obtain ⟨x,hx⟩ := hold
  obtain ⟨p,hp⟩ := M.connected i none hi (some x) hx
  cases p with
  | @cons _ z _ hnz p =>
    cases z with
    | none => exact hnz.elim
    | some z => exact ⟨z,hp _ (by simp),hnz⟩

/-- Suppressing the inserted vertex reflects every model all of whose
branches contain at least one original vertex. -/
noncomputable def MinorModel.contractSubdivision {I : Type*} {F : SimpleGraph I}
    {G : SimpleGraph V} {u v : V} (M : MinorModel F (subdivideEdge G u v))
    (huv : G.Adj u v) (hold : ∀ i, ∃ x, some x ∈ M.branch i) : MinorModel F G where
  branch := fun i => {x | some x ∈ M.branch i}
  nonempty := hold
  disjoint := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj =>
      Set.disjoint_left.mp (M.disjoint i j hij) hi hj)
  connected := by
    intro i x hx y hy
    obtain ⟨p,hp⟩ := M.connected i (some x) hx (some y) hy
    exact contract_subdivision_walk huv (M.branch i) p hp
  adjacent := by
    intro i j hij
    have hne : i ≠ j := hij.ne
    have endpoint_edge : ∀ x y : V, some x ∈ M.branch i → some y ∈ M.branch j →
        (x = u ∨ x = v) → (y = u ∨ y = v) → G.Adj x y := by
      intro x y hx hy hxu hyv
      have hxy : x ≠ y := by
        intro h; subst y
        exact hne (M.branch_unique hx hy)
      rcases hxu with rfl | rfl <;> rcases hyv with rfl | rfl
      · exact (hxy rfl).elim
      · exact huv
      · exact huv.symm
      · exact (hxy rfl).elim
    obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent i j hij
    cases x with
    | none =>
      cases y with
      | none => exact hxy.elim
      | some y =>
        obtain ⟨x,hx,hxe⟩ := subdivision_branch_endpoint M i hx (hold i)
        exact ⟨x,hx,y,hy,endpoint_edge x y hx hy hxe hxy⟩
    | some x =>
      cases y with
      | none =>
        obtain ⟨y,hy,hye⟩ := subdivision_branch_endpoint M j hy (hold j)
        exact ⟨x,hx,y,hy,endpoint_edge x y hx hy hxy hye⟩
      | some y => exact ⟨x,hx,y,hy,hxy.1⟩

end MinorFreeSpanners

namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The inserted vertex has at most the two old endpoints as neighbors. -/
theorem subdivision_new_degree_le_two (G : SimpleGraph V) (u v : V) :
    (subdivideEdge G u v).degree none ≤ 2 := by
  classical
  have hs : (subdivideEdge G u v).neighborFinset none ⊆ {some u,some v} := by
    intro x hx
    have ha : (subdivideEdge G u v).Adj none x := by simpa using hx
    cases x with
    | none => exact ha.elim
    | some x =>
      have he : x = u ∨ x = v := ha
      rcases he with rfl | rfl <;> simp
  exact (Finset.card_le_card hs).trans Finset.card_le_two

/-- A clique model of order at least four cannot use only the inserted
vertex for one of its branches. -/
theorem clique_subdivision_branches_old {G : SimpleGraph V} {u v : V}
    {h : ℕ} (hh : 4 ≤ h) (M : MinorModel (⊤ : SimpleGraph (Fin h))
      (subdivideEdge G u v)) : ∀ i, ∃ x, some x ∈ M.branch i := by
  intro i
  by_contra hn
  push_neg at hn
  have honly : ∀ x ∈ M.branch i, x = none := by
    intro x hx
    cases x with
    | none => rfl
    | some x => exact (hn x hx).elim
  have hd := (M.singleton_branch_degree i none honly).trans
    (subdivision_new_degree_le_two G u v)
  simp only [complete_graph_degree, Fintype.card_fin] at hd
  omega

/-- Subdividing an actual edge preserves K_h-minor exclusion for h ≥ 4.
This is an actual minor-model reflection, not a numerical invariant. -/
theorem CliqueMinorFree.subdivideEdge {G : SimpleGraph V} {u v : V}
    {h : ℕ} (hG : CliqueMinorFree G h) (huv : G.Adj u v) (hh : 4 ≤ h) :
    CliqueMinorFree (subdivideEdge G u v) h := by
  rintro ⟨M⟩
  exact hG ⟨M.contractSubdivision huv (clique_subdivision_branches_old hh M)⟩

end MinorFreeSpanners
