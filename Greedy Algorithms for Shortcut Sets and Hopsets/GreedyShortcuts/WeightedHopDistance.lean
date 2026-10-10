import GreedyShortcuts.WeightedPerturbation

/-!
Weighted hop-distance and insertion-sensitive hopset augmentation. Hop-distance
is the minimum number of edges among actual shortest weighted walks. An inserted
closure edge receives the original graph distance, including when it is parallel
to a heavier original edge. Uninserted original edge weights are never replaced.
-/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph
open GreedyShortcuts.DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_minHopShortest (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (h : Reachable G s t) : ∃ p : DWalk s t, MinHopShortest G w p := by
  obtain ⟨w', _, hpairs⟩ := exists_unique_minhop_reweighting G w
  obtain ⟨p, _, hp⟩ := hpairs s t h
  exact ⟨p, hp⟩

noncomputable def minHopPath (G : V → V → Prop) (w : V → V → ℝ≥0)
    (s t : V) (h : Reachable G s t) : DWalk s t :=
  Classical.choose (exists_minHopShortest G w h)

theorem minHopPath_spec (G : V → V → Prop) (w : V → V → ℝ≥0)
    (s t : V) (h : Reachable G s t) : MinHopShortest G w (minHopPath G w s t h) :=
  Classical.choose_spec (exists_minHopShortest G w h)

noncomputable def distance (G : V → V → Prop) (w : V → V → ℝ≥0)
    (s t : V) : ℝ≥0 := by
  classical
  exact if h : Reachable G s t then
    ⟨cost w (minHopPath G w s t h), cost_nonneg w _⟩ else 0

noncomputable def hopDistance (G : V → V → Prop) (w : V → V → ℝ≥0)
    (s t : V) : ℕ := by
  classical
  exact if h : Reachable G s t then (minHopPath G w s t h).length else 0

theorem distance_eq (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (h : Reachable G s t) :
    (distance G w s t : ℝ) = cost w (minHopPath G w s t h) := by
  simp [distance, h]
  rfl

theorem hopDistance_eq (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (h : Reachable G s t) :
    hopDistance G w s t = (minHopPath G w s t h).length := by
  simp [hopDistance, h]

theorem distance_le_cost (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (p : DWalk s t) (hp : Allowed G p) :
    (distance G w s t : ℝ) ≤ cost w p := by
  rw [distance_eq G w ⟨p, hp⟩]
  exact (minHopPath_spec G w s t ⟨p, hp⟩).1.2 p hp

theorem Shortest.cost_eq_distance {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : DWalk s t} (hp : Shortest G w p) :
    cost w p = (distance G w s t : ℝ) := by
  rw [distance_eq G w ⟨p, hp.1⟩]
  exact hp.cost_eq (minHopPath_spec G w s t ⟨p, hp.1⟩).1

theorem shortest_iff_cost_eq_distance {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : DWalk s t} (hp : Allowed G p) :
    Shortest G w p ↔ cost w p = (distance G w s t : ℝ) := by
  refine ⟨Shortest.cost_eq_distance, ?_⟩
  intro he
  exact ⟨hp, fun q hq => he.le.trans (distance_le_cost G w q hq)⟩

theorem hopDistance_le_of_shortest {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : DWalk s t} (hp : Shortest G w p) :
    hopDistance G w s t ≤ p.length := by
  rw [hopDistance_eq G w ⟨p, hp.1⟩]
  exact (minHopPath_spec G w s t ⟨p, hp.1⟩).2 p hp

theorem MinHopShortest.length_eq_hopDistance {G : V → V → Prop}
    {w : V → V → ℝ≥0} {s t : V} {p : DWalk s t} (hp : MinHopShortest G w p) :
    p.length = hopDistance G w s t := by
  apply le_antisymm _ (hopDistance_le_of_shortest hp.1)
  rw [hopDistance_eq G w ⟨p, hp.1.1⟩]
  exact hp.2 _ (minHopPath_spec G w s t ⟨p, hp.1.1⟩).1

@[simp] theorem distance_self (G : V → V → Prop) (w : V → V → ℝ≥0) (s : V) :
    distance G w s s = 0 := by
  have h := distance_le_cost G w (Walk.nil : DWalk s s) (allowed_nil G s)
  have he : (distance G w s s : ℝ) = 0 := le_antisymm (by simpa using h)
    (distance G w s s).coe_nonneg
  exact_mod_cast he

@[simp] theorem hopDistance_self (G : V → V → Prop) (w : V → V → ℝ≥0) (s : V) :
    hopDistance G w s s = 0 := by
  have h := hopDistance_le_of_shortest (G := G) (w := w)
    (p := (Walk.nil : DWalk s s))
    ⟨allowed_nil G s, fun q _ => by simpa using cost_nonneg w q⟩
  simpa using h

theorem hopDistance_lt_card (G : V → V → Prop) (w : V → V → ℝ≥0)
    {s t : V} (h : Reachable G s t) : hopDistance G w s t < Fintype.card V := by
  rw [hopDistance_eq G w h]
  exact (minHopPath_spec G w s t h).isPath.length_lt

theorem distance_edge_le {G : V → V → Prop} (w : V → V → ℝ≥0)
    {s t : V} (h : G s t) : distance G w s t ≤ w s t := by
  by_cases he : s = t
  · subst t
    simp
  · have hh := distance_le_cost G w
      (Walk.cons (by simpa using he) Walk.nil : DWalk s t) (by simp [h])
    exact_mod_cast (show (distance G w s t : ℝ) ≤ (w s t : ℝ) by simpa using hh)

/-- Exactly the inserted hopedges receive their closure distance. -/
noncomputable def augmentWeight (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (s t : V) : ℝ≥0 :=
  if (s, t) ∈ H then distance G w s t else w s t

@[simp] theorem augmentWeight_empty (G : V → V → Prop) (w : V → V → ℝ≥0) :
    augmentWeight G w ∅ = w := by
  funext s t
  simp [augmentWeight]

theorem augmentWeight_of_mem (G : V → V → Prop) (w : V → V → ℝ≥0)
    {H : Finset (V × V)} {s t : V} (h : (s,t) ∈ H) :
    augmentWeight G w H s t = distance G w s t := by simp [augmentWeight, h]

theorem augmentWeight_of_not_mem (G : V → V → Prop) (w : V → V → ℝ≥0)
    {H : Finset (V × V)} {s t : V} (h : (s,t) ∉ H) :
    augmentWeight G w H s t = w s t := by simp [augmentWeight, h]

/-- A heavier parallel original edge really changes weight when its hopedge
is inserted; it has not been silently replaced by its closure distance before. -/
theorem augmentWeight_parallel_insertion (G : V → V → Prop) (w : V → V → ℝ≥0)
    {H : Finset (V × V)} {s t : V} (hnot : (s,t) ∉ H)
    (hheavy : distance G w s t < w s t) :
    augmentWeight G w (insert (s,t) H) s t < augmentWeight G w H s t := by
  simpa [augmentWeight, hnot] using hheavy

theorem augmentWeight_le_on_edge {G : V → V → Prop} (w : V → V → ℝ≥0)
    (H : Finset (V × V)) {s t : V} (h : G s t) :
    augmentWeight G w H s t ≤ w s t := by
  classical
  unfold augmentWeight
  split_ifs
  · exact distance_edge_le w h
  · exact le_rfl

/-- Every augmented walk has an original directed walk of the same cost,
by expanding each inserted closure edge into an original shortest path. -/
theorem augment_walk_lift (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (hH : H ⊆ candidates G)
    {s t : V} (p : DWalk s t) (hp : Allowed (augment G H) p) :
    ∃ q : DWalk s t, Allowed G q ∧ cost w q = cost (augmentWeight G w H) p := by
  classical
  induction p with
  | nil => exact ⟨.nil, allowed_nil G _, by simp⟩
  | @cons s u t h p ih =>
    have ha := (allowed_cons (augment G H) h p).mp hp
    obtain ⟨q, hq, hcost⟩ := ih ha.2
    by_cases he : (s,u) ∈ H
    · have hr := ((mem_candidates G (s,u)).mp (hH he)).2
      let r := minHopPath G w s u hr
      have hs := (minHopPath_spec G w s u hr).1
      refine ⟨r.append q, (allowed_append G r q).mpr ⟨hs.1, hq⟩, ?_⟩
      rw [cost_append, cost_cons, hcost, augmentWeight_of_mem G w he]
      exact congrArg (fun x : ℝ => x + cost (augmentWeight G w H) p)
        hs.cost_eq_distance
    · have hsu : G s u := ha.1.resolve_right he
      refine ⟨.cons h q, (allowed_cons G h q).mpr ⟨hsu, hq⟩, ?_⟩
      simp only [cost_cons, hcost, augmentWeight_of_not_mem G w he]

/-- Original walks remain available and can only become cheaper after insertion. -/
theorem cost_augment_le (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) {s t : V} (p : DWalk s t) (hp : Allowed G p) :
    cost (augmentWeight G w H) p ≤ cost w p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have ha := (allowed_cons G h p).mp hp
    simp only [cost_cons]
    exact add_le_add (by exact_mod_cast augmentWeight_le_on_edge w H ha.1) (ih ha.2)

/-- Insertion of genuine closure edges preserves exact weighted distances. -/
theorem distance_augment (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (s t : V) :
    distance (augment G H) (augmentWeight G w H) s t = distance G w s t := by
  classical
  by_cases hr : Reachable G s t
  · have ha := reachable_augment G H hr
    let p := minHopPath G w s t hr
    have hp := (minHopPath_spec G w s t hr).1
    let q := minHopPath (augment G H) (augmentWeight G w H) s t ha
    have hq := (minHopPath_spec (augment G H) (augmentWeight G w H) s t ha).1
    obtain ⟨r, hrg, hrc⟩ := augment_walk_lift G w H hH q hq.1
    apply NNReal.coe_injective
    apply le_antisymm
    · calc
        (distance (augment G H) (augmentWeight G w H) s t : ℝ)
            ≤ cost (augmentWeight G w H) p :=
          distance_le_cost _ _ p (allowed_mono (fun _ _ => Or.inl) hp.1)
        _ ≤ cost w p := cost_augment_le G w H p hp.1
        _ = (distance G w s t : ℝ) := hp.cost_eq_distance
    · calc
        (distance G w s t : ℝ) ≤ cost w r := distance_le_cost G w r hrg
        _ = cost (augmentWeight G w H) q := hrc
        _ = (distance (augment G H) (augmentWeight G w H) s t : ℝ) :=
          hq.cost_eq_distance
  · have ha : ¬ Reachable (augment G H) s t :=
      fun ha => hr ((reachable_augment_iff G H hH s t).mp ha)
    simp [distance, hr, ha]

end GreedyShortcuts.WeightedPaths
