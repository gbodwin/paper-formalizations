import MinorFreeSpanners.MinorRestriction
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Any two vertices on the support of a walk are connected within that support. -/
theorem walk_support_connected {a b x y : V} (p : G.Walk a b)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ q : G.Walk x y, ∀ z ∈ q.support, z ∈ p.support := by
  classical
  refine ⟨(p.takeUntil x hx).reverse.append (p.takeUntil y hy),?_⟩
  intro z hz
  rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact p.support_takeUntil_subset_support hx (by simpa using hz)
  · exact p.support_takeUntil_subset_support hy hz

/-- Two singleton branches and an internal path give an actual triangle minor. -/
noncomputable def triangleModel_of_internal_walk {u v x y : V}
    (huv : G.Adj u v) (hux : G.Adj u x) (hyv : G.Adj y v)
    (p : G.Walk x y) (hu : u ∉ p.support) (hv : v ∉ p.support) :
    MinorModel (⊤ : SimpleGraph (Fin 3)) G := by
  let B : Fin 3 → Set V := fun i => if i = 0 then {u} else if i = 1 then {v}
    else {z | z ∈ p.support}
  have h01 : ∃ a ∈ B 0, ∃ b ∈ B 1, G.Adj a b :=
    ⟨u,by simp [B],v,by simp [B],huv⟩
  have h10 : ∃ a ∈ B 1, ∃ b ∈ B 0, G.Adj a b :=
    ⟨v,by simp [B],u,by simp [B],huv.symm⟩
  have h02 : ∃ a ∈ B 0, ∃ b ∈ B 2, G.Adj a b :=
    ⟨u,by simp [B],x,by simpa [B] using p.start_mem_support,hux⟩
  have h20 : ∃ a ∈ B 2, ∃ b ∈ B 0, G.Adj a b :=
    ⟨x,by simpa [B] using p.start_mem_support,u,by simp [B],hux.symm⟩
  have h12 : ∃ a ∈ B 1, ∃ b ∈ B 2, G.Adj a b :=
    ⟨v,by simp [B],y,by simpa [B] using p.end_mem_support,hyv.symm⟩
  have h21 : ∃ a ∈ B 2, ∃ b ∈ B 1, G.Adj a b :=
    ⟨y,by simpa [B] using p.end_mem_support,v,by simp [B],hyv⟩
  refine {branch := B,nonempty := ?_,disjoint := ?_,connected := ?_,adjacent := ?_}
  · intro i
    fin_cases i
    · exact ⟨u,by simp [B]⟩
    · exact ⟨v,by simp [B]⟩
    · exact ⟨x,by simpa [B] using p.start_mem_support⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [B,Set.disjoint_left,huv.ne,huv.ne']
    all_goals intro a ha he; subst a; contradiction
  · intro i a ha b hb
    fin_cases i
    · simp only [B,if_pos rfl,Set.mem_singleton_iff] at ha hb
      subst a; subst b
      exact ⟨.nil,by simp [B]⟩
    · simp [B] at ha hb
      subst a; subst b
      exact ⟨.nil,by simp [B]⟩
    · have ha' : a ∈ p.support := by simpa [B] using ha
      have hb' : b ∈ p.support := by simpa [B] using hb
      obtain ⟨q,hq⟩ := walk_support_connected p ha' hb'
      exact ⟨q,by simpa [B] using hq⟩
  · intro i j hij
    have hne : i ≠ j := hij
    fin_cases i <;> fin_cases j <;>
      first | exact (hne rfl).elim | exact h01 | exact h10 | exact h02 | exact h20 | exact h12 | exact h21

/-- An edge plus a simple alternative path contains a genuine K₃ minor. -/
theorem triangle_minor_of_alternative_path {u v : V} (huv : G.Adj u v)
    (p : G.Walk u v) (hp : p.IsPath) (he : s(u,v) ∉ p.edges) :
    Nonempty (MinorModel (⊤ : SimpleGraph (Fin 3)) G) := by
  cases p with
  | nil => exact (huv.ne rfl).elim
  | @cons _ x _ hux q =>
    have hq := (Walk.cons_isPath_iff _ _).mp hp
    cases q with
    | nil => exact (he (by simp)).elim
    | @cons _ z _ hxz q =>
      let t := Walk.cons hxz q
      have ht : ¬ t.Nil := Walk.not_nil_cons
      have hsupport : t.dropLast.support ++ [v] = t.support := Walk.support_dropLast_concat ht
      have hu : u ∉ t.dropLast.support := by
        intro hu
        apply hq.2
        rw [← hsupport]
        simp [hu]
      have hv : v ∉ t.dropLast.support := by
        have hd : (t.dropLast.support ++ [v]).Nodup := hsupport.symm ▸ hq.1.support_nodup
        exact fun hv => (List.nodup_append.mp hd).2.2 v hv v (by simp) rfl
      exact ⟨triangleModel_of_internal_walk huv hux (t.adj_penultimate ht) t.dropLast hu hv⟩

/-- Every actual cycle yields a K₃ branch-set minor. -/
theorem triangle_minor_of_cycle {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    Nonempty (MinorModel (⊤ : SimpleGraph (Fin 3)) G) := by
  cases p with
  | nil => exact (Walk.not_isCycle_nil hp).elim
  | cons h p =>
    have hpath := (Walk.cons_isCycle_iff _ _).mp hp
    exact triangle_minor_of_alternative_path h.symm p hpath.1 (by simpa [Sym2.eq_swap] using hpath.2)

/-- Excluding K₃ minors forces an actual forest. -/
theorem CliqueMinorFree.isAcyclic {G : SimpleGraph V} (hG : CliqueMinorFree G 3) :
    G.IsAcyclic := by
  intro u p hp
  exact hG (triangle_minor_of_cycle p hp)

end MinorFreeSpanners
