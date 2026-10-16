import LightEFTSpanners.EvenTightUncrossing

namespace LightEFTSpanners.EvenSplitting
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Symmetric union-max requirements obey the skew-supermodular inequality. -/
theorem skew_of_symmetric_union_max (r : Finset V → ℤ)
    (hsym : ∀ S,r Sᶜ=r S) (hunion : ∀ S T,r (S∪T)≤max (r S) (r T)) :
    SkewSupermodular r := by
  intro S T
  have h₁ := hunion (S∩T) (S\T)
  have h₂ := hunion (S∩T) (T\S)
  have h₃ := hunion ((S∪T)ᶜ) (T\S)
  have h₄ := hunion ((S∪T)ᶜ) (S\T)
  have he₁ : (S∩T)∪(S\T)=S := by ext x; simp; tauto
  have he₂ : (S∩T)∪(T\S)=T := by ext x; simp; tauto
  have he₃ : (S∪T)ᶜ∪(T\S)=Sᶜ := by ext x; simp; tauto
  have he₄ : (S∪T)ᶜ∪(S\T)=Tᶜ := by ext x; simp; tauto
  rw [he₁] at h₁
  rw [he₂] at h₂
  rw [he₃,hsym,hsym] at h₃
  rw [he₄,hsym,hsym] at h₄
  omega

/-- The actual required pair relation, including either orientation of a
separated pair. It need not be an equivalence relation. -/
def Separates (P : V → V → Prop) (S : Finset V) : Prop :=
  ∃ a b,P a b ∧ ((a∈S ∧ b∉S) ∨ (b∈S ∧ a∉S))

theorem separates_compl (P : V → V → Prop) (S : Finset V) :
    Separates P Sᶜ ↔ Separates P S := by
  unfold Separates
  simp only [mem_compl,not_not]
  constructor <;> rintro ⟨a,b,h,hab⟩ <;> exact ⟨a,b,h,by tauto⟩

omit [Fintype V] in
theorem separates_union (P : V → V → Prop) (S T : Finset V)
    (h : Separates P (S∪T)) : Separates P S ∨ Separates P T := by
  obtain ⟨a,b,hp,hab⟩ := h
  simp only [mem_union] at hab
  by_cases ha : a∈S <;> by_cases hb : b∈S
  · right; exact ⟨a,b,hp,by tauto⟩
  · left; exact ⟨a,b,hp,Or.inl ⟨ha,hb⟩⟩
  · left; exact ⟨a,b,hp,Or.inr ⟨hb,ha⟩⟩
  · right; exact ⟨a,b,hp,by tauto⟩

noncomputable def requirement (P : V → V → Prop) (k : ℕ) (S : Finset V) : ℤ :=
  by classical exact if Separates P S then 2*k else 0

theorem requirement_compl (P : V → V → Prop) (k : ℕ) (S : Finset V) :
    requirement P k Sᶜ=requirement P k S := by
  classical
  simp only [requirement,separates_compl]

omit [Fintype V] in
theorem requirement_union_max (P : V → V → Prop) (k : ℕ) (S T : Finset V) :
    requirement P k (S∪T)≤max (requirement P k S) (requirement P k T) := by
  classical
  by_cases h : Separates P (S∪T)
  · rcases separates_union P S T h with hs | ht
    · simp [requirement,h,hs]
    · simp [requirement,h,ht]
  · simp only [requirement,h,ite_false]
    positivity

theorem requirement_skew (P : V → V → Prop) (k : ℕ) :
    SkewSupermodular (requirement P k) :=
  skew_of_symmetric_union_max _ (requirement_compl P k) (requirement_union_max P k)

omit [Fintype V] [DecidableEq V] in
theorem requirement_even (P : V → V → Prop) (k : ℕ) (S : Finset V) :
    Even (requirement P k S) := by
  classical
  unfold requirement
  split_ifs
  · exact ⟨k,by omega⟩
  · exact ⟨0,by omega⟩
end LightEFTSpanners.EvenSplitting
