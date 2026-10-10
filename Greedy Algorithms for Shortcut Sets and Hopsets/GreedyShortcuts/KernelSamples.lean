import GreedyShortcuts.FiniteHitting
import GreedyShortcuts.KernelLift
import GreedyShortcuts.CanonicalSegments

/-! Deterministic finite sampling by a proved greedy hitting set. The kernel
contains sampled vertices and short original-reachability edges. -/
namespace GreedyShortcuts.KernelSamples
open Finset SimpleGraph DirectedPaths CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

def HitsLong (G : V → V → Prop) (S : Finset V) (r : ℕ) : Prop :=
  ∀ s t (p : DWalk s t),Optimal G (fun _ _ => 1) p → r ≤ p.length →
    ∃ v ∈ p.support,v ∈ S

noncomputable def pathSet (G : V → V → Prop) (d : V × V) : Finset V := by
  classical
  exact if hr : Reachable G d.1 d.2 then (canonical G d.1 d.2 hr).support.toFinset else ∅

noncomputable def longPairs (G : V → V → Prop) (r : ℕ) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun d => Reachable G d.1 d.2 ∧ r ≤ hopDist G d.1 d.2)

theorem pathSet_card (G : V → V → Prop) (r : ℕ) {d : V × V} (hd : d ∈ longPairs G r) :
    r+1 ≤ (pathSet G d).card := by
  classical
  have hh := (Finset.mem_filter.mp hd).2
  simp only [pathSet,dite_eq_left hh.1,List.toFinset_card_of_nodup
    (canonical_optimal G d.1 d.2 hh.1).2.1.support_nodup,Walk.length_support]
  simpa only [hopDist_eq G hh.1] using Nat.add_le_add_right hh.2 1

noncomputable def samples (G : V → V → Prop) (r : ℕ) : Finset V :=
  FiniteHitting.output (longPairs G r) (pathSet G) (r+1) (by omega)
    (fun _ hd => pathSet_card G r hd)

theorem samples_card (G : V → V → Prop) (r : ℕ) :
    (samples G r).card ≤ (Nat.log 2 (longPairs G r).card+1)*(Fintype.card V/(r+1)+1) :=
  FiniteHitting.output_card _ _ _ _ _

theorem samples_hit (G : V → V → Prop) (r : ℕ) : HitsLong G (samples G r) r := by
  classical
  intro s t p hp hlen
  have hr : Reachable G s t := ⟨p,hp.1⟩
  have he : p = canonical G s t hr := hp.unique (canonical_optimal G s t hr)
  have hd : (s,t) ∈ longPairs G r := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hr,by simpa only [hopDist_eq G hr,← he] using hlen⟩
  obtain ⟨v,hv,hs⟩ := FiniteHitting.output_hits (longPairs G r) (pathSet G) (r+1)
    (by omega) (fun _ hd => pathSet_card G r hd) hd
  refine ⟨v,?_,hs⟩
  simpa only [pathSet,dite_eq_left hr,← he,List.mem_toFinset] using hv

theorem hit_interval {G : V → V → Prop} {S : Finset V} {r : ℕ} (hS : HitsLong G S r)
    {s t : V} {p : DWalk s t} (hp : Optimal G (fun _ _ => 1) p)
    (i : ℕ) (hi : i+r ≤ p.length) :
    ∃ j,i ≤ j ∧ j ≤ i+r ∧ p.getVert j ∈ S := by
  let q := segment p i (i+r) (by omega)
  have hq := optimal_segment hp i (i+r) (by omega)
  have hlen : q.length = r := by
    change (segment p i (i+r) (by omega)).length = r
    rw [segment_length p (show i ≤ i+r by omega) hi]
    omega
  obtain ⟨v,hv,hvs⟩ := hS _ _ q hq (by omega)
  obtain ⟨k,hkv,hk⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  have hk' : k ≤ r := by simpa only [hlen] using hk
  refine ⟨i+k,by omega,by omega,?_⟩
  have he : q.getVert k = p.getVert (i+k) := segment_getVert p (by omega) (by omega)
  rw [he] at hkv
  simpa only [hkv] using hvs

def relation (G : V → V → Prop) (S : Finset V) (r : ℕ) (a b : S) : Prop :=
  Reachable G a.val b.val ∧ hopDist G a.val b.val ≤ r+1

theorem reachable_of_optimal {G : V → V → Prop} {S : Finset V} {r : ℕ}
    (hS : HitsLong G S r) (n : ℕ) :
    ∀ a b : S,∀ p : DWalk a.val b.val,p.length = n →
      Optimal G (fun _ _ => 1) p → Reachable (relation G S r) a b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b p hlen hp
    by_cases hs : n ≤ r+1
    · exact reachable_edge ⟨⟨p,hp.1⟩,(hopDist_le_walk G p hp.1).trans (by omega)⟩
    · obtain ⟨i,hi,hir,his⟩ := hit_interval hS hp 1 (by omega)
      let c : S := ⟨p.getVert i,his⟩
      have hc : relation G S r a c := by
        refine ⟨⟨p.take i,hp.subwalk (p.isSubwalk_take i) |>.1⟩,?_⟩
        exact (hopDist_le_walk G (p.take i) (hp.subwalk (p.isSubwalk_take i)).1).trans
          (by simp only [Walk.take_length];omega)
      have hd := ih (p.drop i).length (by simp only [Walk.drop_length];omega)
        c b (p.drop i) rfl (hp.subwalk (p.isSubwalk_drop i))
      exact reachable_trans (reachable_edge hc) hd

noncomputable def kernel {G : V → V → Prop} {S : Finset V} {r : ℕ}
    (hS : HitsLong G S r) : KernelLift.Kernel G S (2*r) (2*r+2) where
  embed := Subtype.val
  injective := Subtype.val_injective
  relation := relation G S r
  expand := by
    intro a b hab
    exact ⟨canonical G a.val b.val hab.1,(canonical_optimal G a.val b.val hab.1).1,
      by simpa only [← hopDist_eq G hab.1] using hab.2.trans (by omega)⟩
  cover := by
    intro s t hr
    let p := canonical G s t hr
    have hp : Optimal G (fun _ _ => 1) p := canonical_optimal G s t hr
    by_cases hs : p.length ≤ 2*r
    · exact Or.inl (by simpa only [hopDist_eq G hr] using hs)
    · obtain ⟨i,hi,hir,his⟩ := hit_interval hS hp 0 (by omega)
      obtain ⟨j,hj,hjr,hjs⟩ := hit_interval hS hp (p.length-r) (by omega)
      have hij : i ≤ j := by omega
      let a : S := ⟨p.getVert i,his⟩
      let b : S := ⟨p.getVert j,hjs⟩
      have hleft := (hp.subwalk (p.isSubwalk_take i)).1
      have hright := (hp.subwalk (p.isSubwalk_drop j)).1
      refine Or.inr ⟨a,b,⟨p.take i,hleft⟩,?_,?_,⟨p.drop j,hright⟩,?_⟩
      · exact (hopDist_le_walk G (p.take i) hleft).trans (by simp only [Walk.take_length];omega)
      · exact reachable_of_optimal hS (segment p i j hij).length a b
          (segment p i j hij) rfl (optimal_segment hp i j hij)
      · exact (hopDist_le_walk G (p.drop j) hright).trans (by simp only [Walk.drop_length];omega)

/-- The actual deterministic hitting set supplies every field of the kernel;
no external existence or geometric-cover hypothesis remains. -/
noncomputable def sampleKernel (G : V → V → Prop) (r : ℕ) :
    KernelLift.Kernel G (samples G r) (2*r) (2*r+2) := kernel (samples_hit G r)

theorem samples_card_le (G : V → V → Prop) (r : ℕ) :
    (samples G r).card ≤ (Nat.log 2 ((Fintype.card V)^2)+1)*(Fintype.card V/(r+1)+1) := by
  have hQ : (longPairs G r).card ≤ (Fintype.card V)^2 := by
    simpa only [Fintype.card_prod,pow_two] using Finset.card_le_univ (longPairs G r)
  exact (samples_card G r).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.log_mono_right hQ) 1))

end GreedyShortcuts.KernelSamples
