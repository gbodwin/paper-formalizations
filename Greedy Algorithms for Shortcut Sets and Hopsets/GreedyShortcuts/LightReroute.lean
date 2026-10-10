import GreedyShortcuts.CanonicalSavings

/-! Native directed-walk rerouting for the light-intersection branch. -/
namespace GreedyShortcuts.LightReroute

open Finset SimpleGraph DirectedPaths CanonicalSegments ShortcutWalk
open SuffixWindowPath CanonicalSavings
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Follow a demand prefix, take the new edge into the base path, follow that
base path forward to the demand suffix, and finish along the old demand. -/
theorem hop_after_reroute {G : V → V → Prop} {s t x y : V}
    {p : DWalk s t} (hp : Allowed G p) {a c : ℕ} (ha : a ≤ p.length)
    {r : DWalk x y} (hr : Allowed G r) (hy : y = p.getVert c)
    (hne : p.getVert a ≠ x) :
    hopDist (augment G {(p.getVert a,x)}) s t ≤ a+1+r.length+(p.length-c) := by
  let r' : DWalk x (p.getVert c) := r.copy rfl hy
  have hr' : Allowed G r' := by subst y; exact hr
  have hedge : (⊤ : SimpleGraph V).Adj (p.getVert a) x := by simpa using hne
  let walk := (p.take a).append (.cons hedge (r'.append (p.drop c)))
  have hmono : ∀ u v, G u v → augment G {(p.getVert a,x)} u v := fun _ _ => Or.inl
  have hw : Allowed (augment G {(p.getVert a,x)}) walk := by
    apply (allowed_append (augment G {(p.getVert a,x)}) (p.take a) (.cons hedge (r'.append (p.drop c)))).mpr
    refine ⟨allowed_mono hmono (allowed_subwalk hp (p.isSubwalk_take a)),?_⟩
    apply (allowed_cons (augment G {(p.getVert a,x)}) hedge (r'.append (p.drop c))).mpr
    refine ⟨Or.inr (by simp),?_⟩
    apply (allowed_append (augment G {(p.getVert a,x)}) r' (p.drop c)).mpr
    exact ⟨allowed_mono hmono hr',allowed_mono hmono (allowed_subwalk hp (p.isSubwalk_drop c))⟩
  have hh := hopDist_le_walk _ walk hw
  simpa [walk,r',Nat.min_eq_left ha,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- A last-quarter intersection and first-quarter source give a large actual
potential decrement, even though the shortcut need not lie on the demand. -/
theorem reroute_saving {G : V → V → Prop} {s t x y : V}
    {p : DWalk s t} (hp : Optimal G (fun _ _ => 1) p) {a c β : ℕ}
    (hβ : 8 ≤ β) (hactive : β < p.length) (ha : a < suffixSize p)
    (hc : suffixOffset p ≤ c) (hc' : c ≤ p.length)
    {r : DWalk x y} (hr : Allowed G r) (hshort : r.length+1 ≤ β/8)
    (hy : y = p.getVert c) (hne : p.getVert a ≠ x) :
    β ≤ 4*demandDrop G β (p.getVert a,x) (s,t) := by
  have hs : suffixSize p ≤ p.length+1 := by dsimp [suffixSize]; omega
  have ha' : a ≤ p.length := by omega
  have hh := hop_after_reroute hp.1 ha' hr hy hne
  have hcon := GraphGreedy.contribution_le β (hopDist (augment G {(p.getVert a,x)}) s t)
  unfold demandDrop
  rw [hopDist_eq_length hp,GraphGreedy.contribution,if_pos hactive]
  dsimp only [Prod.fst,Prod.snd]
  dsimp [suffixSize,suffixOffset] at *
  omega

end GreedyShortcuts.LightReroute
