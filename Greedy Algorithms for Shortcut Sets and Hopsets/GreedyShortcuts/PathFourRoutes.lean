import GreedyShortcuts.PathMedianWitness

/-! Four literal nondecreasing legs, with equality represented by a zero-hop
walk. These are route certificates for constructed edges, not distance axioms. -/
namespace GreedyShortcuts.PathFour
open Finset SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking

def Leg (E : Finset (ℕ × ℕ)) (i j : ℕ) : Prop := i=j ∨ (i,j)∈E

def Route (E : Finset (ℕ × ℕ)) (i j : ℕ) : Prop :=
  ∃ a b c,Leg E i a ∧ Leg E a b ∧ Leg E b c ∧ Leg E c j

theorem leg_refl (E : Finset (ℕ × ℕ)) (i : ℕ) : Leg E i i := Or.inl rfl

theorem route_refl (E : Finset (ℕ × ℕ)) (i : ℕ) : Route E i i :=
  ⟨i,i,i,leg_refl E i,leg_refl E i,leg_refl E i,leg_refl E i⟩

theorem leg_mono {E F : Finset (ℕ × ℕ)} (hEF : E⊆F) {i j : ℕ} (h : Leg E i j) : Leg F i j :=
  h.imp_right (fun he => hEF he)

theorem route_mono {E F : Finset (ℕ × ℕ)} (hEF : E⊆F) {i j : ℕ} (h : Route E i j) : Route F i j := by
  obtain ⟨a,b,c,h1,h2,h3,h4⟩ := h
  exact ⟨a,b,c,leg_mono hEF h1,leg_mono hEF h2,leg_mono hEF h3,leg_mono hEF h4⟩

theorem leg_shift (a : ℕ) {E : Finset (ℕ × ℕ)} {i j : ℕ} (h : Leg E i j) :
    Leg (PathMedian.shift a E) (a+i) (a+j) := by
  rcases h with rfl | he
  · exact Or.inl rfl
  · exact Or.inr (Finset.mem_image.mpr ⟨(i,j),he,rfl⟩)

theorem route_shift (a : ℕ) {E : Finset (ℕ × ℕ)} {i j : ℕ} (h : Route E i j) :
    Route (PathMedian.shift a E) (a+i) (a+j) := by
  obtain ⟨x,y,z,h1,h2,h3,h4⟩ := h
  exact ⟨a+x,a+y,a+z,leg_shift a h1,leg_shift a h2,leg_shift a h3,leg_shift a h4⟩

theorem median_route (d m i j : ℕ) (hsize : m ≤ 2^d) (hij : i ≤ j) (hj : j < m) :
    Route (PathMedian.edges d m) i j := by
  obtain ⟨z,_,_,h1,h2⟩ := PathMedian.two_legs d m i j hsize hij hj
  exact ⟨z,z,z,h1,leg_refl _ _,leg_refl _ _,h2⟩

end GreedyShortcuts.PathFour
