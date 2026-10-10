import GreedyShortcuts.SuffixIntersections

/-! A shortcut joining two points on a canonical DAG path saves the same
number of hops in every canonical path containing those points. -/
namespace GreedyShortcuts.CanonicalSavings

open scoped NNReal
open Finset SimpleGraph DirectedPaths CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem hopDist_eq_length {G : V → V → Prop} {s t : V} {p : DWalk s t}
    (hp : Optimal G (fun _ _ => 1) p) : hopDist G s t = p.length := by
  rw [hopDist_eq G ⟨p,hp.1⟩]
  exact congrArg Walk.length ((canonical_optimal G s t ⟨p,hp.1⟩).unique hp)

theorem common_segment_length {G : V → V → Prop} (hG : Acyclic G)
    {w : V → V → ℝ≥0} {s t u v : V} {q : DWalk s t} {p : DWalk u v}
    (hq : Optimal G w q) (hp : Optimal G w p)
    {i j a b : ℕ} (hij : i < j) (hj : j ≤ q.length)
    (ha : a ≤ p.length) (hb : b ≤ p.length)
    (hea : p.getVert a = q.getVert i) (heb : p.getVert b = q.getVert j) :
    a < b ∧ b-a = j-i := by
  have hab := common_order hG hq.1 hq.2.1 hp.1 hij hj hea heb
  have heq : segment q i j hij.le = (segment p a b hab.le).copy hea heb :=
    (optimal_segment hq i j hij.le).unique
      (optimal_copy (optimal_segment hp a b hab.le) hea heb)
  have hl := congrArg Walk.length heq
  simp only [Walk.length_copy,segment_length q hij.le hj,segment_length p hab.le hb] at hl
  exact ⟨hab,hl.symm⟩

noncomputable def demandDrop (G : V → V → Prop) (β : ℕ) (e d : V × V) : ℕ :=
  GraphGreedy.contribution β (hopDist G d.1 d.2) -
    GraphGreedy.contribution β (hopDist (augment G {e}) d.1 d.2)

/-- This is the graph-specific heavy-case saving, with no progress premise.
Both shortcut endpoints really lie on the active path, and consistent
subpaths identify their separation with that along the short base path. -/
theorem common_shortcut_saving {G : V → V → Prop} (hG : Acyclic G)
    {s t u v : V} {q : DWalk s t} {p : DWalk u v}
    (hq : Optimal G (fun _ _ => 1) q) (hp : Optimal G (fun _ _ => 1) p)
    {β i j : ℕ} (hactive : β < p.length) (hij : i < j) (hj : j ≤ q.length)
    (hi : q.getVert i ∈ p.support) (hj' : q.getVert j ∈ p.support) :
    j-i-1 ≤ demandDrop G β (edgeAt q (i,j)) (u,v) := by
  obtain ⟨a,hea,ha⟩ := Walk.mem_support_iff_exists_getVert.mp hi
  obtain ⟨b,heb,hb⟩ := Walk.mem_support_iff_exists_getVert.mp hj'
  obtain ⟨hab,hlen⟩ := common_segment_length hG hq hp hij hj ha hb hea heb
  have he : edgeAt p (a,b) = edgeAt q (i,j) := Prod.ext hea heb
  have hnew := hop_after_shortcut (G:=G) (H:=∅)
    (p:=p) (allowed_mono (fun _ _ => Or.inl) hp.1)
    hp.2.1 hab hb
  rw [he] at hnew
  change hopDist (augment G {edgeAt q (i,j)}) u v ≤ a+1+(p.length-b) at hnew
  have hc := GraphGreedy.contribution_le β (hopDist (augment G {edgeAt q (i,j)}) u v)
  unfold demandDrop
  rw [hopDist_eq_length hp,GraphGreedy.contribution,if_pos hactive]
  dsimp only [Prod.fst,Prod.snd]
  omega

end GreedyShortcuts.CanonicalSavings
