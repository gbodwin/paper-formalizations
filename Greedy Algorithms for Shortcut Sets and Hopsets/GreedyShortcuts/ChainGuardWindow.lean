import GreedyShortcuts.ChainGuardCone
import GreedyShortcuts.FiniteGuardDescent

/-! Actual bad end-window replacement and finite descent inside one fixed
source cone. This constructs a target without short rebased end windows;
counting a large edge-saving rectangle is a subsequent obligation. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

def BadEndWindow (H : Finset (V × V)) (s t : V) (k : ℕ) : Prop :=
  ∃ u v, ∃ p : DWalk s u, ∃ q : DWalk u v, ∃ r : DWalk v t,
    Allowed (T.graph H s) ((p.append q).append r) ∧
    T.count ((p.append q).append r)=T.distance H s t ∧
    T.count p≤k ∧ T.distance H s t≤T.distance H s v+k ∧
    T.distance H u v<4*k

/-- A genuine cheap end-window gives an important earlier target with small
length loss and actual additive depletion of the unchanged source cone. -/
theorem badEndWindow_step {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} {k : ℕ} (hlarge : 6*k≤T.distance H s t)
    (hbad : T.BadEndWindow H s t k) :
    ∃ z, (s,z) ∈ T.important ∧ Reachable T.G z t ∧
      (T.coneChains s z).card+T.distance H s t≤(T.coneChains s t).card+k ∧
      T.distance H s t≤T.distance H s z+5*k := by
  obtain ⟨u,v,p,q,r,hall,hmin,hp,hlate,hcheap⟩ := hbad
  have hpq := (allowed_append _ _ _).mp hall
  have hparts := (allowed_append _ _ _).mp hpq.1
  have hsu : Reachable T.G s u :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p,allowed_mono (fun _ _ h => h.1) hparts.1⟩
  have huv : Reachable T.G u v :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q,allowed_mono (fun _ _ h => h.1) hparts.2⟩
  have hvt : Reachable T.G v t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨r,allowed_mono (fun _ _ h => h.1) hpq.2⟩
  have hpu := T.distance_le_walk H hsu p hparts.1
  rcases T.distance_guard_dichotomy hH hsu huv with htriangle | ⟨z,hz,_,hzv,hguard,hzd⟩
  · omega
  · refine ⟨z,hz,reachable_trans hzv hvt,?_,by omega⟩
    have hall' : Allowed (T.graph H s) (p.append (q.append r)) := by
      simpa only [Walk.append_assoc] using hall
    have hdep := T.guard_cone_depletion hH p (q.append r) hall' hguard (reachable_trans hzv hvt)
    have hmin' : T.count (p.append (q.append r))=T.distance H s t := by
      simpa only [Walk.append_assoc] using hmin
    rw [hmin'] at hdep
    omega

/-- An actual important target in the original cone admits no cheap end
window. The small-loss guard process is proved to terminate by finite rank,
without assuming cubic progress or rebased optimality. -/
theorem exists_stable_window_target {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s t : V} (hst : (s,t) ∈ T.important) (L k : ℕ)
    (hL : 0<L) (hk : 0<k) (hdist : L≤T.distance H s t)
    (hscale : 64*(T.coneChains s t).card*k≤L^2) :
    ∃ z, (s,z) ∈ T.important ∧ Reachable T.G z t ∧
      L≤2*T.distance H s z ∧ ¬ T.BadEndWindow H s z k := by
  classical
  let A := {z : V // (s,z) ∈ T.important ∧ Reachable T.G z t}
  let rank : A → ℕ := fun z => (T.coneChains s z.val).card
  let dist : A → ℕ := fun z => T.distance H s z.val
  let good : A → Prop := fun z => ¬T.BadEndWindow H s z.val k
  let x₀ : A := ⟨t,hst,reachable_refl T.G t⟩
  have hLK : L≤(T.coneChains s t).card := by
    obtain ⟨p,hp,hpc⟩ := T.distance_spec H (T.important_spec hst).1
    have hc := Finset.card_le_card (T.chainSet_subset_cone hH p hp)
    change T.count p≤_ at hc
    omega
  have hkL : 64*k≤L := by
    have hm := Nat.mul_le_mul_right (64*k) hLK
    nlinarith
  have step : ∀ x : A, L≤2*dist x → ¬good x →
      ∃ y : A,rank y+dist x≤rank x+k ∧ dist x≤dist y+5*k := by
    intro x hx hbad
    have hb : T.BadEndWindow H s x.val k := by simpa only [good,not_not] using hbad
    obtain ⟨z,hz,hzx,hr,hd⟩ := T.badEndWindow_step hH (by dsimp [dist] at hx; omega) hb
    exact ⟨⟨z,hz,reachable_trans hzx x.property.2⟩,hr,hd⟩
  obtain ⟨z,hgood,hz⟩ := FiniteGuardDescent.exists_good rank dist good L
    (T.coneChains s t).card k hL hk hLK hscale step x₀ (by rfl) hdist
  exact ⟨z.val,z.property.1,z.property.2,hz,hgood⟩

end GreedyShortcuts.ChainDistance.Context
