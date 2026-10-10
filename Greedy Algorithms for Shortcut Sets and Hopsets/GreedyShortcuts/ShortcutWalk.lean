import GreedyShortcuts.GraphGreedy

/-! Actual directed-walk replacement by one shortcut, and the finite rectangle
of shortcuts that repairs one active demand. -/
namespace GreedyShortcuts.ShortcutWalk

open SimpleGraph Finset DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem allowed_subwalk {G : V → V → Prop} {s t u v : V}
    {p : DWalk s t} {q : DWalk u v} (hp : Allowed G p) (hq : q.IsSubwalk p) :
    Allowed G q := by
  obtain ⟨l, r, heq⟩ := hq
  subst p
  exact ((allowed_append G l q).mp ((allowed_append G _ r).mp hp).1).2

def edgeAt {s t : V} (p : DWalk s t) (ij : ℕ × ℕ) : V × V :=
  (p.getVert ij.1, p.getVert ij.2)

theorem vertices_ne {s t : V} {p : DWalk s t} (hp : p.IsPath)
    {i j : ℕ} (hij : i < j) (hj : j ≤ p.length) : p.getVert i ≠ p.getVert j := by
  intro heq
  have hh := hp.getVert_injOn (show i ≤ p.length by omega) hj heq
  omega

theorem reachable_segment {G : V → V → Prop} {s t : V}
    {p : DWalk s t} (hp : Allowed G p) {i j : ℕ} (hij : i ≤ j) :
    Reachable G (p.getVert i) (p.getVert j) := by
  let q := (p.take j).drop i
  have hq : Allowed G q :=
    allowed_subwalk (allowed_subwalk hp (p.isSubwalk_take j)) ((p.take j).isSubwalk_drop i)
  have heq : (p.take j).getVert i = p.getVert i := by
    rw [Walk.take_getVert, Nat.min_eq_right hij]
  exact ⟨q.copy heq rfl, by simpa [Allowed] using hq⟩

theorem edgeAt_mem_candidates {G : V → V → Prop} {H : Finset (V × V)}
    (hH : H ⊆ candidates G) {s t : V} {p : DWalk s t}
    (hp : Allowed (augment G H) p) (hpath : p.IsPath)
    {i j : ℕ} (hij : i < j) (hj : j ≤ p.length) :
    edgeAt p (i, j) ∈ candidates G := by
  apply (mem_candidates G _).mpr
  refine ⟨vertices_ne hpath hij hj, ?_⟩
  exact (reachable_augment_iff G H hH _ _).mp (reachable_segment hp hij.le)

/-- Replacing an interior segment by a single added edge gives a real allowed
walk with at most `i + 1 + (length - j)` hops. -/
theorem hop_after_shortcut {G : V → V → Prop} {H : Finset (V × V)}
    {s t : V} {p : DWalk s t} (hp : Allowed (augment G H) p) (hpath : p.IsPath)
    {i j : ℕ} (hij : i < j) (hj : j ≤ p.length) :
    hopDist (augment G (insert (edgeAt p (i, j)) H)) s t ≤ i + 1 + (p.length - j) := by
  let J := insert (edgeAt p (i, j)) H
  have hmono : ∀ u v, augment G H u v → augment G J u v :=
    fun _ _ he => he.elim Or.inl (fun he => Or.inr (Finset.mem_insert_of_mem he))
  have ha : (⊤ : SimpleGraph V).Adj (p.getVert i) (p.getVert j) := by
    simpa using vertices_ne hpath hij hj
  let q := (p.take i).append (.cons ha (p.drop j))
  have hq : Allowed (augment G J) q := by
    refine (allowed_append (augment G J) (p.take i) (.cons ha (p.drop j))).mpr ?_
    refine ⟨allowed_mono hmono (allowed_subwalk hp (p.isSubwalk_take i)), ?_⟩
    refine (allowed_cons (augment G J) ha (p.drop j)).mpr ?_
    refine ⟨Or.inr ?_, allowed_mono hmono (allowed_subwalk hp (p.isSubwalk_drop j))⟩
    simp [J, edgeAt]
  have hh := hopDist_le_walk (augment G J) q hq
  simpa [q, Nat.min_eq_left (show i ≤ p.length by omega), Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, J] using hh

def indexRectangle (L β : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (β / 4 + 1) ×ˢ Finset.Icc (L - β / 4) L

theorem rectangle_indices {L β i j : ℕ} (hβ : 4 ≤ β) (hL : β < L)
    (h : (i, j) ∈ indexRectangle L β) :
    i < j ∧ j ≤ L ∧ i + 1 + (L - j) ≤ β := by
  simp only [indexRectangle, Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at h
  omega

theorem rectangle_card (L β : ℕ) (hL : β ≤ L) :
    (indexRectangle L β).card = (β / 4 + 1) ^ 2 := by
  rw [indexRectangle, Finset.card_product,
    Finset.card_range, Nat.card_Icc]
  have hq : β / 4 ≤ L := (Nat.div_le_self _ _).trans hL
  have heq : L + 1 - (L - β / 4) = β / 4 + 1 := by omega
  rw [heq, pow_two]

def repairEdges {s t : V} (p : DWalk s t) (β : ℕ) : Finset (V × V) :=
  (indexRectangle p.length β).image (edgeAt p)

theorem repairEdges_card {s t : V} {p : DWalk s t} (hp : p.IsPath)
    (β : ℕ) (hβ : 4 ≤ β) (hL : β < p.length) :
    (repairEdges p β).card = (β / 4 + 1) ^ 2 := by
  rw [repairEdges, Finset.card_image_of_injOn]
  · exact rectangle_card _ _ hL.le
  · intro ij hij kl hkl heq
    have h1 := rectangle_indices hβ hL hij
    have h2 := rectangle_indices hβ hL hkl
    apply Prod.ext
    · exact hp.getVert_injOn (show ij.1 ≤ p.length by omega)
        (show kl.1 ≤ p.length by omega) (congrArg Prod.fst heq)
    · exact hp.getVert_injOn h1.2.1 h2.2.1 (congrArg Prod.snd heq)

theorem repairEdges_subset {G : V → V → Prop} {H : Finset (V × V)}
    (hH : H ⊆ candidates G) {s t : V} {p : DWalk s t}
    (hp : Allowed (augment G H) p) (hpath : p.IsPath)
    (β : ℕ) (hβ : 4 ≤ β) (hL : β < p.length) :
    repairEdges p β ⊆ candidates G := by
  intro e he
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp he
  have hi := rectangle_indices hβ hL hij
  exact edgeAt_mem_candidates hH hp hpath hi.1 hi.2.1

theorem repairEdges_repair {G : V → V → Prop} {H : Finset (V × V)}
    {s t : V} {p : DWalk s t} (hp : Allowed (augment G H) p) (hpath : p.IsPath)
    (β : ℕ) (hβ : 4 ≤ β) (hL : β < p.length) {e : V × V}
    (he : e ∈ repairEdges p β) :
    hopDist (augment G (insert e H)) s t ≤ β := by
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp he
  have hi := rectangle_indices hβ hL hij
  exact (hop_after_shortcut hp hpath hi.1 hi.2.1).trans hi.2.2

end GreedyShortcuts.ShortcutWalk
