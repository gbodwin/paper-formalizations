import GreedyShortcuts.ShortcutWalk

/-! Canonical directed-path segments and the DAG-only contiguous-intersection
property used in the heavy-intersection part of Section 3. Self loops are
irrelevant to native walks and hop distances. -/
namespace GreedyShortcuts.CanonicalSegments

open SimpleGraph DirectedPaths ShortcutWalk
open scoped NNReal
open LinearDistancePreservers.ConsistentTiebreaking

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No positive-length directed closed walk. -/
def Acyclic (G : V → V → Prop) : Prop :=
  ∀ s (p : DWalk s s), Allowed G p → p.length = 0

theorem acyclic_iff_reachable_antisymm (G : V → V → Prop) :
    Acyclic G ↔ ∀ s t, Reachable G s t → Reachable G t s → s = t := by
  constructor
  · intro h s t ⟨p, hp⟩ ⟨q, hq⟩
    have hz := h s (p.append q) ((allowed_append G p q).mpr ⟨hp, hq⟩)
    cases p with
    | nil => rfl
    | cons ha p => simp at hz
  · intro h s p hp
    cases p with
    | nil => rfl
    | @cons s u s ha p =>
      have hh := (allowed_cons G ha p).mp hp
      have he := h s u (reachable_edge hh.1) ⟨p, hh.2⟩
      exact (ha.ne he).elim

theorem acyclic_augment {G : V → V → Prop} (hG : Acyclic G)
    {H : Finset (V × V)} (hH : H ⊆ candidates G) : Acyclic (augment G H) := by
  apply (acyclic_iff_reachable_antisymm _).mpr
  intro s t hst hts
  exact (acyclic_iff_reachable_antisymm G).mp hG s t
    ((reachable_augment_iff G H hH s t).mp hst)
    ((reachable_augment_iff G H hH t s).mp hts)

def segment {s t : V} (p : DWalk s t) (i j : ℕ) (hij : i ≤ j) :
    DWalk (p.getVert i) (p.getVert j) :=
  ((p.take j).drop i).copy (by rw [Walk.take_getVert, Nat.min_eq_right hij]) rfl

theorem segment_isSubwalk {s t : V} (p : DWalk s t) (i j : ℕ) (hij : i ≤ j) :
    (segment p i j hij).IsSubwalk p := by
  have hh := ((p.take j).isSubwalk_drop i).trans (p.isSubwalk_take j)
  simpa only [segment, Walk.copy_rfl_rfl] using hh.copy
    (show (p.take j).getVert i = p.getVert i by rw [Walk.take_getVert, Nat.min_eq_right hij])
    rfl rfl rfl

theorem segment_length {s t : V} (p : DWalk s t) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ p.length) : (segment p i j hij).length = j - i := by
  simp [segment, Nat.min_eq_left hj]

theorem segment_getVert {s t : V} (p : DWalk s t) {i j k : ℕ} (hij : i ≤ j)
    (hk : k ≤ j - i) : (segment p i j hij).getVert k = p.getVert (i + k) := by
  simp [segment, Walk.drop_getVert, Walk.take_getVert, Nat.min_eq_right (show i + k ≤ j by omega)]

theorem mem_segment {s t : V} (p : DWalk s t) {i j k : ℕ}
    (hij : i ≤ j) (hik : i ≤ k) (hkj : k ≤ j) :
    p.getVert k ∈ (segment p i j hij).support := by
  have hh := (segment p i j hij).getVert_mem_support (k - i)
  rw [segment_getVert p hij (by omega), Nat.add_sub_of_le hik] at hh
  exact hh

theorem segment_support {s t : V} (p : DWalk s t) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ p.length) :
    (segment p i j hij).support.toFinset = (Finset.Icc i j).image p.getVert := by
  ext v
  simp only [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hv
    obtain ⟨k, hkv, hk⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    have hk' : k ≤ j - i := by simpa only [segment_length p hij hj] using hk
    refine ⟨i + k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa only [segment_getVert p hij hk'] using hkv
  · rintro ⟨k, hk, rfl⟩
    exact mem_segment p hij (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2

theorem segment_sum {s t : V} {p : DWalk s t} (hp : p.IsPath)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) (weight : V → ℕ) :
    (∑ v ∈ (segment p i j hij).support.toFinset, weight v) =
      ∑ k ∈ Finset.Icc i j, weight (p.getVert k) := by
  rw [segment_support p hij hj]
  apply Finset.sum_image
  intro a ha b hb heq
  exact hp.getVert_injOn ((Finset.mem_Icc.mp ha).2.trans hj)
    ((Finset.mem_Icc.mp hb).2.trans hj) heq

theorem optimal_copy {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t u v : V} {p : DWalk s t} (hp : Optimal G w p) (hs : s = u) (ht : t = v) :
    Optimal G w (p.copy hs ht) := by
  subst u
  subst v
  exact hp

theorem optimal_segment {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t : V} {p : DWalk s t} (hp : Optimal G w p) (i j : ℕ) (hij : i ≤ j) :
    Optimal G w (segment p i j hij) := hp.subwalk (segment_isSubwalk p i j hij)

/-- In a DAG, two directed paths cannot traverse two common vertices in
opposite orders. -/
theorem common_order {G : V → V → Prop} (hG : Acyclic G)
    {s t u v : V} {p : DWalk s t} {q : DWalk u v}
    (hp : Allowed G p) (hpp : p.IsPath) (hq : Allowed G q)
    {i j a b : ℕ} (hij : i < j) (hj : j ≤ p.length)
    (ha : q.getVert a = p.getVert i) (hb : q.getVert b = p.getVert j) : a < b := by
  by_contra hn
  have hba : b ≤ a := by omega
  have hforward := reachable_segment hp hij.le
  have hback := reachable_segment hq hba
  rw [ha, hb] at hback
  have heq := (acyclic_iff_reachable_antisymm G).mp hG _ _ hforward hback
  exact vertices_ne hpp hij hj heq

/-- The intersection of two consistently chosen directed shortest paths in
a DAG is order-convex along either path. -/
theorem intersection_convex {G : V → V → Prop} (hG : Acyclic G)
    {w : V → V → ℝ≥0} {s t u v : V} {p : DWalk s t} {q : DWalk u v}
    (hp : Optimal G w p) (hq : Optimal G w q)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ p.length)
    (hiQ : p.getVert i ∈ q.support) (hkQ : p.getVert k ∈ q.support) :
    p.getVert j ∈ q.support := by
  by_cases hik : i = k
  · have hj : j = i := by omega
    simpa [hj] using hiQ
  · have hik' : i < k := by omega
    obtain ⟨a, ha, _⟩ := Walk.mem_support_iff_exists_getVert.mp hiQ
    obtain ⟨b, hb, _⟩ := Walk.mem_support_iff_exists_getVert.mp hkQ
    have hab := common_order hG hp.1 hp.2.1 hq.1 hik' hk ha hb
    let r := (segment q a b hab.le).copy ha hb
    have hr : r.IsSubwalk q := by
      simpa only [Walk.copy_rfl_rfl] using (segment_isSubwalk q a b hab.le).copy ha hb rfl rfl
    have heq : segment p i k (by omega) = r :=
      (optimal_segment hp i k (by omega)).unique (hq.subwalk hr)
    have hm := mem_segment p (show i ≤ k by omega) hij hjk
    rw [heq] at hm
    exact (Walk.isSubwalk_iff_support_isInfix.mp hr).subset hm

end GreedyShortcuts.CanonicalSegments
