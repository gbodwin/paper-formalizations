import LengthExpander.DirectedDemandMatching

/-! Push a finite integral demand through a vertex projection. Total mass is
preserved, row/column budgets scale by exact fibre cardinality, and all
positive output pairs lift to positive input pairs. -/
namespace LengthExpander
open Finset
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [Fintype V] [Fintype W]

noncomputable def vertexFiber (π : W → V) (u : V) : Finset W := univ.filter (fun x => π x = u)

@[simp] theorem mem_vertexFiber (π : W → V) (u : V) (x : W) :
    x ∈ vertexFiber π u ↔ π x = u := by simp [vertexFiber]

theorem sum_vertexFiber (π : W → V) (f : W → ℕ) :
    ∑ u, ∑ x ∈ vertexFiber π u, f x = ∑ x, f x := by
  classical
  simp only [vertexFiber,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

noncomputable def pushDemand (π : W → V) (D : Demand W) : Demand V :=
  fun u v => ∑ x ∈ vertexFiber π u, ∑ y ∈ vertexFiber π v, D x y

theorem pushDemand_row (π : W → V) (D : Demand W) (u : V) :
    ∑ v, pushDemand π D u v = ∑ x ∈ vertexFiber π u, ∑ y, D x y := by
  classical
  unfold pushDemand
  rw [sum_comm]
  exact sum_congr rfl (fun x _ => sum_vertexFiber π (D x))

theorem pushDemand_column (π : W → V) (D : Demand W) (v : V) :
    ∑ u, pushDemand π D u v = ∑ y ∈ vertexFiber π v, ∑ x, D x y := by
  classical
  unfold pushDemand
  calc
    _ = ∑ u, ∑ y ∈ vertexFiber π v, ∑ x ∈ vertexFiber π u, D x y :=
      sum_congr rfl (fun _ _ => sum_comm)
    _ = ∑ y ∈ vertexFiber π v, ∑ u, ∑ x ∈ vertexFiber π u, D x y := sum_comm
    _ = _ := sum_congr rfl (fun y _ => sum_vertexFiber π (fun x => D x y))

theorem pushDemand_size (π : W → V) (D : Demand W) :
    demandSize (pushDemand π D) = demandSize D := by
  unfold demandSize
  simp_rw [pushDemand_row]
  exact sum_vertexFiber π (fun x => ∑ y, D x y)

theorem pushDemand_respects (π : W → V) {D : Demand W} {B : ℕ}
    (hD : Respects D (fun _ => B)) :
    Respects (pushDemand π D) (fun u => (vertexFiber π u).card * B) := by
  constructor
  · intro u
    rw [pushDemand_row]
    exact (sum_le_sum (fun x _ => hD.1 x)).trans (by simp)
  · intro u
    rw [pushDemand_column]
    exact (sum_le_sum (fun x _ => hD.2 x)).trans (by simp)

theorem pushDemand_positive (π : W → V) {D : Demand W} {u v : V}
    (h : 0 < pushDemand π D u v) :
    ∃ x y, π x = u ∧ π y = v ∧ 0 < D x y := by
  obtain ⟨x,hx,hxD⟩ := (sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp h
  obtain ⟨y,hy,hxy⟩ := (sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hxD
  exact ⟨x,y,mem_vertexFiber π u x |>.mp hx,mem_vertexFiber π v y |>.mp hy,hxy⟩

variable {A : NodeWeight V}

noncomputable def copyFiberEquiv (u : V) :
    {x : DirectedCopies A // copyVertex x = u} ≃ (Fin (A u) ⊕ Fin (A u)) where
  toFun x := by
    obtain ⟨x,hx⟩ := x
    rcases x with ⟨v,i⟩ | ⟨v,i⟩
    · change v = u at hx
      subst v
      exact Sum.inl i
    · change v = u at hx
      subst v
      exact Sum.inr i
  invFun x := match x with
    | Sum.inl i => ⟨Sum.inl ⟨u,i⟩,rfl⟩
    | Sum.inr i => ⟨Sum.inr ⟨u,i⟩,rfl⟩
  left_inv x := by
    obtain ⟨x,hx⟩ := x
    rcases x with ⟨v,i⟩ | ⟨v,i⟩ <;> change v = u at hx <;> subst v <;> rfl
  right_inv x := by cases x <;> rfl

theorem copy_vertexFiber_card (u : V) :
    (vertexFiber (copyVertex (A := A)) u).card = 2*A u := by
  classical
  have hc := Fintype.card_congr (copyFiberEquiv (A := A) u)
  simpa [vertexFiber,Fintype.card_subtype,two_mul] using hc

end LengthExpander
