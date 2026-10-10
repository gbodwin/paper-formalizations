import GreedyShortcuts.SCCGreedy

/-! Finite interface and actual application of the cited small-budget kernel
reduction. The interface contains only bounded original-walk expansion and
short prefix/suffix access to kernel pairs. It mentions no greedy algorithm,
shortcut-size conclusion, or new-paper progress lemma. Existence of a small
kernel satisfying this interface is a separate cited-background obligation. -/
namespace GreedyShortcuts.KernelLift

open Finset SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

structure Kernel (G : V → V → Prop) (W : Type*) [Fintype W] [DecidableEq W] (R L : ℕ) where
  embed : W → V
  injective : Function.Injective embed
  relation : W → W → Prop
  expand : ∀ a b,relation a b → ∃ p : DWalk (embed a) (embed b),Allowed G p ∧ p.length ≤ L
  cover : ∀ s t,Reachable G s t → hopDist G s t ≤ R ∨
    ∃ a b,Reachable G s (embed a) ∧ hopDist G s (embed a) ≤ R ∧
      Reachable relation a b ∧ Reachable G (embed b) t ∧ hopDist G (embed b) t ≤ R

/-- Nonvacuity: the whole original vertex set is always a kernel. The cited
sampling theorem is needed for a genuinely smaller cardinality, not for the
logical consistency of this interface. -/
noncomputable def identityKernel (G : V → V → Prop) (R L : ℕ) (hL : 1 ≤ L) :
    Kernel G V R L where
  embed := id
  injective := Function.injective_id
  relation := G
  expand := fun _ _ h => by
    obtain ⟨p,hp,hp1⟩ := DirectedLift.edge_walk h
    exact ⟨p,hp,hp1.trans hL⟩
  cover := fun s t hr => Or.inr ⟨s,t,reachable_refl G s,by simp,hr,reachable_refl G t,by simp⟩

namespace Kernel
variable {G : V → V → Prop} {R L : ℕ} (A : Kernel G W R L)

noncomputable def output (β : ℕ) (hβ : 1 ≤ β) : Finset (V × V) :=
  DirectedMap.edges A.embed (SCCGreedy.output A.relation β hβ)

theorem output_legal (β : ℕ) (hβ : 1 ≤ β) : A.output β hβ ⊆ candidates G := by
  intro e he
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp he
  have hh := (mem_candidates A.relation (a,b)).mp (SCCGreedy.output_legal A.relation β hβ hab)
  apply (mem_candidates G _).mpr
  refine ⟨fun he => hh.1 (A.injective he),?_⟩
  exact DirectedLift.reachable A.embed (fun u v huv => by
    obtain ⟨p,hp,_⟩ := A.expand u v huv
    exact ⟨p,hp⟩) hh.2

theorem output_card (β : ℕ) (hβ : 1 ≤ β) :
    (A.output β hβ).card ≤ (SCCGreedy.output A.relation β hβ).card :=
  DirectedMap.edges_card_le _ _

theorem output_card_log_bound (β : ℕ) (hβ : 1 ≤ β)
    (hq : 2 ≤ Fintype.card (SCCQuotient.Component A.relation)) :
    ((A.output β hβ).card : ℝ) ≤ 2*(Fintype.card W:ℝ) +
      4*Real.logb 2 (Fintype.card (SCCQuotient.Component A.relation):ℝ) *
        (16385*(Fintype.card (SCCQuotient.Component A.relation):ℝ)^(3/(2:ℝ))/(β:ℝ)^(3/(2:ℝ)) +
          147456*(Fintype.card (SCCQuotient.Component A.relation):ℝ)^2/(β:ℝ)^3) := by
  exact (Nat.cast_le.mpr (A.output_card β hβ)).trans
    (SCCGreedy.output_card_log_bound A.relation β hβ hq)

theorem output_reachable_iff (β : ℕ) (hβ : 1 ≤ β) (s t : V) :
    Reachable (augment G (A.output β hβ)) s t ↔ Reachable G s t :=
  reachable_augment_iff G _ (A.output_legal β hβ) s t

theorem augmented_expand (β : ℕ) (hβ : 1 ≤ β) (hL : 1 ≤ L) {a b : W}
    (hab : augment A.relation (SCCGreedy.output A.relation β hβ) a b) :
    ∃ p : DWalk (A.embed a) (A.embed b),Allowed (augment G (A.output β hβ)) p ∧ p.length ≤ L := by
  rcases hab with he | he
  · obtain ⟨p,hp,hpL⟩ := A.expand a b he
    exact ⟨p,allowed_mono (fun _ _ => Or.inl) hp,hpL⟩
  · obtain ⟨p,hp,hp1⟩ := DirectedLift.edge_walk (G := augment G (A.output β hβ))
      (s := A.embed a) (t := A.embed b) (Or.inr (DirectedMap.mem_edges _ _ he))
    exact ⟨p,hp,hp1.trans hL⟩

/-- Actual composition of kernel access, SCC preprocessing, DAG greedy, and
walk expansion, with every additive/multiplicative hop cost explicit. -/
theorem output_hop_bound (β : ℕ) (hβ : 1 ≤ β) (hL : 1 ≤ L)
    {s t : V} (hr : Reachable G s t) :
    hopDist (augment G (A.output β hβ)) s t ≤ 2*R + L*(3*β+2) := by
  rcases A.cover s t hr with hshort | ⟨a,b,ha,haR,hab,hb,hbR⟩
  · exact ((hopDist_mono (fun _ _ => Or.inl) hr).trans hshort).trans (by omega)
  · let J := SCCGreedy.output A.relation β hβ
    have hab' := reachable_augment A.relation J hab
    let p := canonical (augment A.relation J) a b hab'
    have hp := canonical_optimal (augment A.relation J) a b hab'
    have hpβ : p.length ≤ 3*β+2 := by
      have h := SCCGreedy.output_hop_bound A.relation β hβ hab
      change hopDist (augment A.relation J) a b ≤ 3*β+2 at h
      simpa only [hopDist_eq _ hab'] using h
    obtain ⟨q,hq,hqL⟩ := DirectedLift.bounded A.embed L (fun _ _ => A.augmented_expand β hβ hL) p hp.1
    let l := canonical G s (A.embed a) ha
    let r := canonical G (A.embed b) t hb
    have hl := (canonical_optimal G s (A.embed a) ha).1
    have hr' := (canonical_optimal G (A.embed b) t hb).1
    have hlR : l.length ≤ R := by simpa only [hopDist_eq _ ha] using haR
    have hrR : r.length ≤ R := by simpa only [hopDist_eq _ hb] using hbR
    have hw := hopDist_le_walk (augment G (A.output β hβ)) (l.append (q.append r))
      ((allowed_append _ _ _).mpr ⟨allowed_mono (fun _ _ => Or.inl) hl,
        (allowed_append _ _ _).mpr ⟨hq,allowed_mono (fun _ _ => Or.inl) hr'⟩⟩)
    have hh := hqL.trans (Nat.mul_le_mul_left L hpβ)
    simp only [Walk.length_append] at hw
    omega

end Kernel
end GreedyShortcuts.KernelLift
