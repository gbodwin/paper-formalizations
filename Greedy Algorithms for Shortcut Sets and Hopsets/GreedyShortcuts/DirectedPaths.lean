import LinearDistancePreservers.ConsistentTiebreaking

/-!
Native directed walks, consistent unweighted shortest paths, and closure-edge
augmentation. The ambient complete simple graph supplies the walk datatype;
`Allowed` checks each directed step against the input relation. Self loops are
irrelevant to reachability and hop distance and are not shortcut candidates.
-/
namespace GreedyShortcuts.DirectedPaths

open SimpleGraph
open LinearDistancePreservers.ConsistentTiebreaking

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev DWalk (s t : V) := (⊤ : SimpleGraph V).Walk s t

def Reachable (G : V → V → Prop) (s t : V) : Prop :=
  ∃ p : DWalk s t, Allowed G p

@[simp] theorem allowed_nil (G : V → V → Prop) (s : V) :
    Allowed G (Walk.nil : DWalk s s) := by simp [Allowed]

@[simp] theorem allowed_cons (G : V → V → Prop) {s u t : V}
    (h : (⊤ : SimpleGraph V).Adj s u) (p : DWalk u t) :
    Allowed G (Walk.cons h p) ↔ G s u ∧ Allowed G p := by
  simp [Allowed, Walk.darts_cons]

theorem reachable_refl (G : V → V → Prop) (s : V) : Reachable G s s :=
  ⟨.nil, allowed_nil G s⟩

theorem reachable_trans {G : V → V → Prop} {s u t : V}
    (hs : Reachable G s u) (ht : Reachable G u t) : Reachable G s t := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  exact ⟨p.append q, (allowed_append G p q).mpr ⟨hp, hq⟩⟩

theorem reachable_edge {G : V → V → Prop} {s t : V} (h : G s t) :
    Reachable G s t := by
  by_cases heq : s = t
  · subst t
    exact reachable_refl G s
  · exact ⟨.cons (by simpa using heq) .nil, by simp [h]⟩

theorem allowed_mono {G H : V → V → Prop}
    (hGH : ∀ s t, G s t → H s t) {s t : V} {p : DWalk s t}
    (hp : Allowed G p) : Allowed H p :=
  fun d hd => hGH d.fst d.snd (hp d hd)

theorem reachable_mono {G H : V → V → Prop}
    (hGH : ∀ s t, G s t → H s t) {s t : V}
    (h : Reachable G s t) : Reachable H s t := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, allowed_mono hGH hp⟩

/-- Replace every step by an actual directed walk in the old graph. -/
theorem reachable_of_lift {G H : V → V → Prop}
    (hGH : ∀ s t, H s t → Reachable G s t) {s t : V}
    (p : DWalk s t) : Allowed H p → Reachable G s t := by
  induction p with
  | nil => exact fun _ => reachable_refl G _
  | @cons s u t h p ih =>
    intro hp
    have hh := (allowed_cons H h p).mp hp
    exact reachable_trans (hGH s u hh.1) (ih hh.2)

noncomputable def canonical (G : V → V → Prop) (s t : V)
    (h : Reachable G s t) : DWalk s t :=
  Classical.choose (exists_optimal G (fun _ _ => 1) s t h)

theorem canonical_optimal (G : V → V → Prop) (s t : V)
    (h : Reachable G s t) : Optimal G (fun _ _ => 1) (canonical G s t h) :=
  Classical.choose_spec (exists_optimal G (fun _ _ => 1) s t h)

theorem unit_cost {s t : V} (p : DWalk s t) :
    (p.darts.map (fun _ => (1 : ℝ))).sum = (p.length : ℝ) := by
  induction p with
  | nil => simp
  | cons h p ih => simpa [Nat.cast_add, add_comm] using congrArg (fun x : ℝ => 1 + x) ih

theorem canonical_min_length (G : V → V → Prop) {s t : V}
    (h : Reachable G s t) (p : DWalk s t) (hp : Allowed G p) :
    (canonical G s t h).length ≤ p.length := by
  have hh := (canonical_optimal G s t h).shortest p hp
  simpa only [NNReal.coe_one, unit_cost, Nat.cast_le] using hh

noncomputable def hopDist (G : V → V → Prop) (s t : V) : ℕ := by
  classical
  exact if h : Reachable G s t then (canonical G s t h).length else 0

theorem hopDist_eq (G : V → V → Prop) {s t : V} (h : Reachable G s t) :
    hopDist G s t = (canonical G s t h).length := by
  simp [hopDist, h]

theorem hopDist_le_walk (G : V → V → Prop) {s t : V}
    (p : DWalk s t) (hp : Allowed G p) : hopDist G s t ≤ p.length := by
  rw [hopDist_eq G ⟨p, hp⟩]
  exact canonical_min_length G ⟨p, hp⟩ p hp

theorem hopDist_lt_card (G : V → V → Prop) {s t : V} (h : Reachable G s t) :
    hopDist G s t < Fintype.card V := by
  rw [hopDist_eq G h]
  exact (canonical_optimal G s t h).2.1.length_lt

theorem hopDist_le_card (G : V → V → Prop) (s t : V) :
    hopDist G s t ≤ Fintype.card V := by
  classical
  by_cases h : Reachable G s t
  · exact (hopDist_lt_card G h).le
  · simp [hopDist, h]

@[simp] theorem hopDist_self (G : V → V → Prop) (s : V) : hopDist G s s = 0 := by
  have hh := hopDist_le_walk G (.nil : DWalk s s) (allowed_nil G s)
  simpa using hh

theorem hopDist_edge {G : V → V → Prop} {s t : V} (h : G s t) :
    hopDist G s t ≤ 1 := by
  by_cases heq : s = t
  · subst t
    simp
  · exact hopDist_le_walk G (.cons (by simpa using heq) .nil) (by simp [h])

/-- Hop distances decrease under insertion, for every previously reachable pair. -/
theorem hopDist_mono {G H : V → V → Prop}
    (hGH : ∀ s t, G s t → H s t) {s t : V} (h : Reachable G s t) :
    hopDist H s t ≤ hopDist G s t := by
  rw [hopDist_eq G h]
  exact hopDist_le_walk H (canonical G s t h)
    (allowed_mono hGH (canonical_optimal G s t h).1)

/-- The chosen directed shortest paths are genuinely consistent on subwalks. -/
theorem canonical_subwalk {G : V → V → Prop} {s t u v : V}
    (h : Reachable G s t) {q : DWalk u v} (hq : q.IsSubwalk (canonical G s t h)) :
    ∃ hq' : Reachable G u v, q = canonical G u v hq' := by
  have ho := (canonical_optimal G s t h).subwalk hq
  exact ⟨⟨q, ho.1⟩, ho.unique (canonical_optimal G u v ⟨q, ho.1⟩)⟩

noncomputable def candidates (G : V → V → Prop) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun e => e.1 ≠ e.2 ∧ Reachable G e.1 e.2

@[simp] theorem mem_candidates (G : V → V → Prop) (e : V × V) :
    e ∈ candidates G ↔ e.1 ≠ e.2 ∧ Reachable G e.1 e.2 := by
  classical
  simp [candidates]

def augment (G : V → V → Prop) (H : Finset (V × V)) (s t : V) : Prop :=
  G s t ∨ (s, t) ∈ H

theorem reachable_augment (G : V → V → Prop) (H : Finset (V × V))
    {s t : V} (h : Reachable G s t) : Reachable (augment G H) s t :=
  reachable_mono (fun _ _ => Or.inl) h

/-- Inserting only closure edges preserves exactly the original reachability. -/
theorem reachable_augment_iff (G : V → V → Prop) (H : Finset (V × V))
    (hH : H ⊆ candidates G) (s t : V) :
    Reachable (augment G H) s t ↔ Reachable G s t := by
  refine ⟨?_, reachable_augment G H⟩
  rintro ⟨p, hp⟩
  apply reachable_of_lift (p := p) (H := augment G H) ?_ hp
  intro u v huv
  rcases huv with huv | huv
  · exact reachable_edge huv
  · exact ((mem_candidates G (u, v)).mp (hH huv)).2

theorem hopDist_augment_antitone (G : V → V → Prop)
    {H J : Finset (V × V)} (hHJ : H ⊆ J) {s t : V} (h : Reachable G s t) :
    hopDist (augment G J) s t ≤ hopDist (augment G H) s t :=
  hopDist_mono (fun _ _ he => he.elim Or.inl (fun he => Or.inr (hHJ he)))
    (reachable_augment G H h)

end GreedyShortcuts.DirectedPaths
