import GreedyShortcuts.WeightedShortcut

/-! Exact expansion of a hopset walk into original shortest paths, retaining
both its expanded hop count and every inserted edge's contiguous subwalk. -/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def expansionLength (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) {s t : V} (p : DWalk s t) : ℕ :=
  (p.darts.map fun d => if (d.fst,d.snd) ∈ H then hopDistance G w d.fst d.snd else 1).sum

@[simp] theorem expansionLength_nil (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (s : V) : expansionLength G w H (Walk.nil : DWalk s s) = 0 := by
  simp [expansionLength]

@[simp] theorem expansionLength_cons (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) {s u t : V} (h : (⊤ : SimpleGraph V).Adj s u) (p : DWalk u t) :
    expansionLength G w H (.cons h p) =
      (if (s,u) ∈ H then hopDistance G w s u else 1) + expansionLength G w H p := by
  simp [expansionLength]

/-- This is stronger than cost preservation alone: each inserted dart expands
into a specified original minimum-hop shortest path, contiguously. -/
theorem augment_walk_lift_refined (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (hH : H ⊆ candidates G)
    {s t : V} (p : DWalk s t) (hp : Allowed (augment G H) p) :
    ∃ q : DWalk s t, Allowed G q ∧ cost w q = cost (augmentWeight G w H) p ∧
      q.length = expansionLength G w H p ∧
      ∀ d ∈ p.darts, ∀ he : (d.fst,d.snd) ∈ H,
        (minHopPath G w d.fst d.snd ((mem_candidates G _).mp (hH he)).2).IsSubwalk q := by
  classical
  induction p with
  | nil => exact ⟨.nil, allowed_nil G _, by simp, by simp, by simp⟩
  | @cons s u t h p ih =>
    have ha := (allowed_cons (augment G H) h p).mp hp
    obtain ⟨q, hq, hcost, hlen, hsub⟩ := ih ha.2
    by_cases he : (s,u) ∈ H
    · have hr := ((mem_candidates G (s,u)).mp (hH he)).2
      let r := minHopPath G w s u hr
      have hs := minHopPath_spec G w s u hr
      refine ⟨r.append q, (allowed_append G r q).mpr ⟨hs.1.1, hq⟩, ?_, ?_, ?_⟩
      · rw [cost_append, cost_cons, hcost, augmentWeight_of_mem G w he]
        exact congrArg (fun x : ℝ => x + cost (augmentWeight G w H) p) hs.1.cost_eq_distance
      · simp only [Walk.length_append, expansionLength_cons, if_pos he, hlen]
        rw [← hopDistance_eq G w hr]
      · intro d hd hmem
        simp only [Walk.darts_cons, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Walk.isSubwalk_of_append_left rfl
        · exact (hsub d hd hmem).trans (Walk.isSubwalk_of_append_right rfl)
    · have hsu : G s u := ha.1.resolve_right he
      refine ⟨.cons h q, (allowed_cons G h q).mpr ⟨hsu, hq⟩, ?_, ?_, ?_⟩
      · simp only [cost_cons, hcost, augmentWeight_of_not_mem G w he]
      · simp only [Walk.length_cons, expansionLength_cons, if_neg he, hlen]
        omega
      · intro d hd hmem
        simp only [Walk.darts_cons, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact (he hmem).elim
        · exact (hsub d hd hmem).cons h

/-- With unique shortest paths, the lifted walk is the original unique path.
Consequently all used hopedges correspond to contiguous pieces of that path. -/
theorem unique_expansion {G : V → V → Prop} {w : V → V → ℝ≥0}
    {H : Finset (V × V)} (hH : H ⊆ candidates G)
    {s t : V} {p q : DWalk s t} (hp : UniqueShortest G w p)
    (hq : Shortest (augment G H) (augmentWeight G w H) q) :
    p.length = expansionLength G w H q ∧
      ∀ d ∈ q.darts, ∀ he : (d.fst,d.snd) ∈ H,
        (minHopPath G w d.fst d.snd ((mem_candidates G _).mp (hH he)).2).IsSubwalk p := by
  obtain ⟨r, hr, hc, hl, hs⟩ := augment_walk_lift_refined G w H hH q hq.1
  have hshort : Shortest G w r := by
    apply (shortest_iff_cost_eq_distance hr).mpr
    rw [hc, hq.cost_eq_distance, distance_augment G w H hH]
  have he := hp.2 r hshort
  simpa only [he] using And.intro hl hs

end GreedyShortcuts.WeightedPaths
