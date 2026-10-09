import DirectedFlowCutGap.MinimumClosureProblem
import DirectedFlowCutGap.IntegralNetworkFlow

/-!
# Finite-capacity reduction from signed closure to directed cut

Required, forbidden, and implication arcs use the explicit capacity
`1 + sum |cost|`. A supplied feasible closure gives a cut below that capacity.
The reduction proves exact cost agreement and transports an actual cut
certificate. It does not assume a max-flow algorithm or its running time.
-/
namespace DirectedFlowCutGap.MinimumClosureCut

open scoped BigOperators
open MinimumClosureProblem IntegralNetworkFlow

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev Vertex (A : Type*) := A ⊕ Bool
abbrev core (a : A) : Vertex A := .inl a
abbrev source : Vertex A := .inr false
abbrev sink : Vertex A := .inr true

def budget (P : Problem A) : ℕ := ∑ a, (P.cost a).natAbs
def barrier (P : Problem A) : ℕ := budget P + 1

def positive (P : Problem A) (a : A) : ℕ := (P.cost a).toNat
def negative (P : Problem A) (a : A) : ℕ := (-P.cost a).toNat

/-- All capacities are explicit nonnegative integers. -/
def capacity (P : Problem A) : Capacity (Vertex A)
  | .inr false, .inl a => negative P a + if a ∈ P.required then barrier P else 0
  | .inl a, .inr true => positive P a + if a ∈ P.forbidden then barrier P else 0
  | .inl a, .inl b => if (a, b) ∈ P.arcs then barrier P else 0
  | _, _ => 0

def lift (T : Finset A) : Finset (Vertex A) := insert source (T.image core)

omit [Fintype A] in
@[simp] theorem core_mem_lift (T : Finset A) (a : A) : core a ∈ lift T ↔ a ∈ T := by
  simp [lift, core, source]

omit [Fintype A] in
@[simp] theorem source_mem_lift (T : Finset A) : (source : Vertex A) ∈ lift T := by simp [lift]
omit [Fintype A] in
@[simp] theorem sink_not_mem_lift (T : Finset A) : (sink : Vertex A) ∉ lift T := by
  simp [lift, source, sink, core]

/-- The finite part of the cut cost, before any violated hard constraints. -/
def finiteCost (P : Problem A) (T : Finset A) : ℕ :=
  (∑ a ∈ T, positive P a) + ∑ a ∈ Tᶜ, negative P a

theorem capacity_le_cutCapacity (c : Capacity (Vertex A)) (Y : Finset (Vertex A))
    {u v : Vertex A} (hu : u ∈ Y) (hv : v ∉ Y) : c u v ≤ cutCapacity c Y := by
  calc
    c u v ≤ ∑ w ∈ Yᶜ, c u w :=
      Finset.single_le_sum (f := fun w => c u w) (fun _ _ => Nat.zero_le _)
        (Finset.mem_compl.mpr hv)
    _ ≤ ∑ z ∈ Y, ∑ w ∈ Yᶜ, c z w :=
      Finset.single_le_sum (f := fun z => ∑ w ∈ Yᶜ, c z w)
        (fun _ _ => Nat.zero_le _) hu

/-- A cut below the explicit barrier cannot violate any closure requirement. -/
theorem closed_of_small_cut (P : Problem A) (T : Finset A)
    (hsmall : cutCapacity (capacity P) (lift T) < barrier P) : P.IsClosed T := by
  refine ⟨?_, Finset.disjoint_left.mpr ?_, ?_⟩
  · intro a ha
    by_contra hat
    have h := capacity_le_cutCapacity (capacity P) (lift T)
      (source_mem_lift T) (show core a ∉ lift T by simpa using hat)
    have hb : barrier P ≤ capacity P source (core a) := by simp [capacity, ha]
    exact (not_le_of_gt hsmall) (hb.trans h)
  · intro a hat haf
    have h := capacity_le_cutCapacity (capacity P) (lift T)
      ((core_mem_lift T a).mpr hat) (sink_not_mem_lift T)
    have hb : barrier P ≤ capacity P (core a) sink := by simp [capacity, haf]
    exact (not_le_of_gt hsmall) (hb.trans h)
  · intro a b hab hat
    by_contra hbt
    have h := capacity_le_cutCapacity (capacity P) (lift T)
      ((core_mem_lift T a).mpr hat) (show core b ∉ lift T by simpa using hbt)
    have hb : barrier P = capacity P (core a) (core b) := by simp [capacity, hab]
    exact (not_le_of_gt hsmall) (by simpa only [← hb] using h)

private theorem core_row (P : Problem A) (T : Finset A) (hT : P.IsClosed T)
    {a : A} (ha : a ∈ T) :
    (∑ v ∈ (lift T)ᶜ, capacity P (core a) v) = positive P a := by
  have haf : a ∉ P.forbidden := fun h => Finset.disjoint_left.mp hT.avoids_forbidden ha h
  calc
    _ = capacity P (core a) sink := by
      apply Finset.sum_eq_single sink
      · intro v hv hvne
        cases v with
        | inl b =>
          have hbt : b ∉ T := by simpa using Finset.mem_compl.mp hv
          have hab : (a, b) ∉ P.arcs := fun h => hbt (hT.follows_arcs a b h ha)
          simp [capacity, hab]
        | inr b => cases b <;> simp_all [sink]
      · intro hs
        exact (hs (Finset.mem_compl.mpr (sink_not_mem_lift T))).elim
    _ = _ := by simp [capacity, haf]

private theorem source_row (P : Problem A) (T : Finset A) (hT : P.IsClosed T) :
    (∑ v ∈ (lift T)ᶜ, capacity P source v) = ∑ a ∈ Tᶜ, negative P a := by
  calc
    _ = ∑ v ∈ Tᶜ.image core, capacity P source v := by
      symm
      apply Finset.sum_subset
      · intro v hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        simpa using ha
      · intro v hv hnot
        cases v with
        | inl a =>
          have ha : a ∈ Tᶜ := by simpa using hv
          exact (hnot (Finset.mem_image.mpr ⟨a, ha, rfl⟩)).elim
        | inr b => cases b <;> rfl
    _ = _ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro a ha
        have har : a ∉ P.required := fun h => (Finset.mem_compl.mp ha) (hT.contains_required h)
        simp [capacity, har]
      · intro a _ b _ h
        exact Sum.inl.inj h

/-- A feasible closure crosses no barrier arc, with exact finite cost. -/
theorem cutCapacity_lift (P : Problem A) (T : Finset A) (hT : P.IsClosed T) :
    cutCapacity (capacity P) (lift T) = finiteCost P T := by
  unfold cutCapacity
  change (∑ u ∈ insert source (T.image core),
    ∑ v ∈ (lift T)ᶜ, capacity P u v) = finiteCost P T
  rw [Finset.sum_insert (by simp [source, core])]
  rw [source_row P T hT, Finset.sum_image]
  · have hrows : (∑ a ∈ T, ∑ v ∈ (lift T)ᶜ, capacity P (core a) v) =
        ∑ a ∈ T, positive P a := Finset.sum_congr rfl (fun a ha => core_row P T hT ha)
    rw [hrows]
    exact Nat.add_comm _ _
  · intro a _ b _ h
    exact Sum.inl.inj h

/-- Every feasible finite cut is bounded by the total absolute input cost. -/
theorem finiteCost_le_budget (P : Problem A) (T : Finset A) : finiteCost P T ≤ budget P := by
  have hp (a : A) : positive P a ≤ (P.cost a).natAbs := by
    rw [← Int.toNat_add_toNat_neg_eq_natAbs]
    exact Nat.le_add_right _ _
  have hn (a : A) : negative P a ≤ (P.cost a).natAbs := by
    rw [← Int.toNat_add_toNat_neg_eq_natAbs]
    exact Nat.le_add_left _ _
  calc
    _ ≤ (∑ a ∈ T, (P.cost a).natAbs) + ∑ a ∈ Tᶜ, (P.cost a).natAbs :=
      Nat.add_le_add (Finset.sum_le_sum (fun a _ => hp a)) (Finset.sum_le_sum (fun a _ => hn a))
    _ = _ := Finset.sum_add_sum_compl T (fun a => (P.cost a).natAbs)

/-- The finite cut objective differs from signed closure cost by a fixed offset. -/
theorem finiteCost_int (P : Problem A) (T : Finset A) :
    (finiteCost P T : ℤ) = P.objective T + ∑ a, (negative P a : ℤ) := by
  have hdecomp (a : A) : (positive P a : ℤ) = P.cost a + (negative P a : ℤ) := by
    have h := Int.toNat_sub_toNat_neg (P.cost a)
    dsimp [positive, negative]
    omega
  have hsplit := Finset.sum_add_sum_compl T (fun a => (negative P a : ℤ))
  unfold finiteCost Problem.objective
  push_cast
  simp_rw [hdecomp]
  rw [Finset.sum_add_distrib]
  rw [← hsplit]
  ring

/-- The augmentation budget comes from one feasible closure, even if required
barrier arcs make the raw outgoing source capacity larger. -/
theorem flow_value_le_budget (P : Problem A) (T : Finset A) (hT : P.IsClosed T)
    (f : Flow (capacity P) source sink) : f.value ≤ (budget P : ℤ) := by
  have h := weak_duality f (lift T) (source_mem_lift T) (sink_not_mem_lift T)
  rw [cutCapacity_lift P T hT] at h
  exact h.trans (by exact_mod_cast finiteCost_le_budget P T)

/-- Extract the core side of a separating cut. -/
def cores (Y : Finset (Vertex A)) : Finset A := Finset.univ.filter fun a => core a ∈ Y

@[simp] theorem mem_cores (Y : Finset (Vertex A)) (a : A) : a ∈ cores Y ↔ core a ∈ Y := by
  simp [cores]

theorem lift_cores (Y : Finset (Vertex A)) (hs : source ∈ Y) (ht : sink ∉ Y) :
    lift (cores Y) = Y := by
  ext v
  cases v with
  | inl a => simp
  | inr b => cases b <;> simp [hs, ht]

/-- An actual minimum-cut certificate gives the exact signed minimum closure.
A supplied feasible closure is used only to establish the finite barrier bound. -/
theorem closure_of_minimum_cut (P : Problem A) (T₀ : Finset A) (hT₀ : P.IsClosed T₀)
    (Y : Finset (Vertex A)) (hs : source ∈ Y) (ht : sink ∉ Y)
    (hmin : ∀ Z, source ∈ Z → sink ∉ Z →
      cutCapacity (capacity P) Y ≤ cutCapacity (capacity P) Z) :
    P.IsClosed (cores Y) ∧ ∀ T, P.IsClosed T → P.objective (cores Y) ≤ P.objective T := by
  have hYsmall : cutCapacity (capacity P) Y < barrier P := by
    have h := hmin (lift T₀) (source_mem_lift T₀) (sink_not_mem_lift T₀)
    rw [cutCapacity_lift P T₀ hT₀] at h
    exact (h.trans (finiteCost_le_budget P T₀)).trans_lt (Nat.lt_succ_self _)
  have hclosed : P.IsClosed (cores Y) := closed_of_small_cut P (cores Y)
    (by simpa only [lift_cores Y hs ht] using hYsmall)
  refine ⟨hclosed, ?_⟩
  intro T hT
  have h := hmin (lift T) (source_mem_lift T) (sink_not_mem_lift T)
  rw [← lift_cores Y hs ht, cutCapacity_lift P (cores Y) hclosed, cutCapacity_lift P T hT] at h
  have h' : (finiteCost P (cores Y) : ℤ) ≤ finiteCost P T := by exact_mod_cast h
  rw [finiteCost_int, finiteCost_int] at h'
  omega

omit [DecidableEq A] in
/-- Explicit network size, before any algorithmic implementation. -/
theorem card_vertex : Fintype.card (Vertex A) = Fintype.card A + 2 := by simp [Vertex]

end DirectedFlowCutGap.MinimumClosureCut
