import LinearDistancePreservers.DirectionObstacle
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-! Quantitative outer ports from mathlib's proved Behrend construction.
The three-layer outer graph needs only two-term average rigidity. It does
not need convex position or rigidity of averages of arbitrary length. -/
namespace LinearDistancePreservers.BehrendPorts
open Finset
attribute [local instance] Classical.propDecidable

/-- No nonconstant arithmetic progression in the indexed port slopes. -/
def TwoRigid {J : Type*} (a : J → ℕ) : Prop :=
  ∀ i j t, a i + a j = 2*a t → i = t ∧ j = t

/-- Any desired number of labels up to the Roth number can be assigned
distinct bounded slopes with the required two-term rigidity. -/
theorem exists_ports {J : Type*} [Fintype J] {R : ℕ}
    (hcard : Fintype.card J ≤ rothNumberNat R) :
    ∃ a : J → ℕ, Function.Injective a ∧ (∀ j, a j < R) ∧ TwoRigid a := by
  classical
  obtain ⟨A,hAR,hA,hfree⟩ := rothNumberNat_spec R
  have hc : Fintype.card J ≤ Fintype.card A := by simpa [hA] using hcard
  let f : J ↪ A := (Function.Embedding.nonempty_of_card_le hc).some
  let a : J → ℕ := fun j => (f j).val
  have hinj : Function.Injective a := Subtype.val_injective.comp f.injective
  refine ⟨a,hinj,fun j => mem_range.mp (hAR (f j).property),?_⟩
  intro i j t he
  have hi : a i = a t := hfree (f i).property (f t).property (f j).property (by
    change a i+a j=a t+a t
    omega)
  exact ⟨hinj hi,hinj (by omega)⟩

/-- A numerical capacity condition suffices: the large progression-free
set is obtained by an actual application of the imported Behrend theorem. -/
theorem exists_ports_of_exp {J : Type*} [Fintype J] {R : ℕ}
    (hcard : (Fintype.card J : ℝ) ≤ (R : ℝ)*Real.exp (-4*Real.sqrt (Real.log R))) :
    ∃ a : J → ℕ, Function.Injective a ∧ (∀ j, a j < R) ∧ TwoRigid a := by
  apply exists_ports
  exact_mod_cast hcard.trans Behrend.roth_lower_bound

/-- A wholly integer capacity bound, useful when selecting explicit
parameters without logarithms, square roots, or asymptotic notation. -/
theorem roth_capacity {p q b : ℕ} (h : p*(q*(b-1)^2+1) ≤ b^q) :
    p ≤ rothNumberNat ((2*b-1)^q) := by
  obtain ⟨s,_,hs⟩ := Behrend.exists_large_sphere_aux q b
  have hden : (0 : ℝ) < (q*(b-1)^2 : ℕ)+1 := by positivity
  have hp : (p : ℝ) ≤ (Behrend.sphere q b s).card := by
    apply le_trans _ hs
    apply (le_div_iff₀ hden).mpr
    exact_mod_cast h
  have hp' : p ≤ (Behrend.sphere q b s).card := by exact_mod_cast hp
  exact hp'.trans (Behrend.card_sphere_le_rothNumberNat q b s)

/-- One-coordinate outer directions attached to the chosen port slopes. -/
def direction {J : Type*} (a : J → ℕ) (j : J) : Unit → ℕ := fun _ => a j

theorem direction_injective {J : Type*} {a : J → ℕ} (ha : Function.Injective a) :
    Function.Injective (direction a) := by
  intro i j h
  exact ha (congrFun h ())

open SimpleGraph DirectionGraph DirectionObstacle
set_option backward.isDefEq.respectTransparency.types false
variable {D J : Type*} {n M k r R : ℕ}

/-- The two-term condition gives outer uniqueness with no wraparound.
Different entering and exiting labels are allowed in the competitor. -/
theorem outer_unique (v : J → D → ℕ) (a : Port D J n → ℕ)
    (hv : ∀ j d, v j d < n) (hinj : Function.Injective v)
    (ha : Function.Injective a) (haR : ∀ j, a j < R) (hM : 3*R ≤ M) (hfree : TwoRigid a) :
    ObstacleProduct.OuterUnique
      (data (M := M) (k := k) v (direction a) hv hinj
        (fun j _ => (haR j).trans_le (by omega)) (direction_injective ha)) := by
  intro b j b' j₁ j₂ hl hr
  have hl' := congrFun hl ()
  have hr' := congrFun hr ()
  change b' () - (a j₁ : ZMod M) = b () - (a j : ZMod M) at hl'
  change b' () + (a j₂ : ZMod M) = b () + (a j : ZMod M) at hr'
  have he : ((a j₁+a j₂ : ℕ) : ZMod M) = ((2*a j : ℕ) : ZMod M) := by
    push_cast
    linear_combination hr' - hl'
  have hs : a j₁+a j₂ = 2*a j := by
    simpa only [ZMod.val_natCast_of_lt (show a j₁+a j₂ < M by have := haR j₁; have := haR j₂; omega),
      ZMod.val_natCast_of_lt (show 2*a j < M by have := haR j; omega)] using congrArg ZMod.val he
  obtain ⟨h1,h2⟩ := hfree j₁ j₂ j hs
  subst j₁ j₂
  exact ⟨sub_left_inj.mp hl,rfl,rfl⟩

end LinearDistancePreservers.BehrendPorts
