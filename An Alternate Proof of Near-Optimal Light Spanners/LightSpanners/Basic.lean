import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Foundations for Bodwin, TheoretiCS 4 (2025), Article 2.
Weights live on unordered vertex pairs; walks are actual mathlib graph walks.
The walk formulation of stretch also handles disconnected input graphs. -/
namespace LightSpanners
open SimpleGraph
variable {V : Type*}

def walkWeight (w : Sym2 V → ℝ) {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : ℝ := (p.edges.map w).sum

@[simp] theorem walkWeight_nil (w : Sym2 V → ℝ) (G : SimpleGraph V) (u : V) :
    walkWeight w (.nil : G.Walk u u) = 0 := by simp [walkWeight]

@[simp] theorem walkWeight_cons (w : Sym2 V → ℝ) {G : SimpleGraph V}
    {u v z : V} (h : G.Adj u v) (p : G.Walk v z) :
    walkWeight w (.cons h p) = w s(u,v) + walkWeight w p := by simp [walkWeight]

@[simp] theorem walkWeight_append (w : Sym2 V → ℝ) {G : SimpleGraph V}
    {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by simp [walkWeight]

@[simp] theorem walkWeight_mapLe (w : Sym2 V → ℝ) {G H : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (h : G ≤ H) :
    walkWeight w (p.mapLe h) = walkWeight w p := by simp [walkWeight]

@[simp] theorem walkWeight_transfer (w : Sym2 V → ℝ) {G H : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (h : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    walkWeight w (p.transfer H h) = walkWeight w p := by simp [walkWeight]

/-- Definition 1.1, expressed by replacing every input walk. -/
def IsSpanner (G H : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) : Prop :=
  H ≤ G ∧ ∀ u v (p : G.Walk u v),
    ∃ q : H.Walk u v, walkWeight w q ≤ t * walkWeight w p

/-- Definition 3.1 without division or a minimum over an empty set of cycles.
For positive weights this says every cycle has normalized weight greater than g. -/
def WeightedGirthAbove (G : SimpleGraph V) (w : Sym2 V → ℝ) (g : ℝ) : Prop :=
  ∀ a (p : G.Walk a a), p.IsCycle →
    ∀ e ∈ p.edges, g * w e < walkWeight w p

/-- Algorithm 1's exact edge test; orientation-independent. -/
def Covered (H : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ) (e : Sym2 V) : Prop :=
  ∀ u v, s(u,v) = e → ∃ p : H.Walk u v, walkWeight w p ≤ t * w e

theorem covered_mono {H K : SimpleGraph V} (hHK : H ≤ K)
    {w : Sym2 V → ℝ} {t : ℝ} {e : Sym2 V} (h : Covered H w t e) :
    Covered K w t e := by
  intro u v he
  obtain ⟨p, hp⟩ := h u v he
  exact ⟨p.mapLe hHK, by simpa using hp⟩

theorem covered_of_mem {H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t : ℝ} (ht : 1 ≤ t) (hw : ∀ e, 0 ≤ w e)
    {e : Sym2 V} (he : e ∈ H.edgeSet) : Covered H w t e := by
  intro u v huv
  have hadj : H.Adj u v := (mem_edgeSet H).mp (huv ▸ he)
  refine ⟨hadj.toWalk, ?_⟩
  simp only [SimpleGraph.Adj.toWalk, walkWeight_cons, walkWeight_nil, add_zero, huv]
  nlinarith [hw e]

theorem covered_edges_spanner {G H : SimpleGraph V} {w : Sym2 V → ℝ}
    {t : ℝ} (hHG : H ≤ G) (h : ∀ e ∈ G.edgeSet, Covered H w t e) :
    IsSpanner G H w t := by
  refine ⟨hHG, ?_⟩
  intro u v p
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons u v z huv p ih =>
    obtain ⟨q, hq⟩ := h s(u,v) ((mem_edgeSet G).mpr huv) u v rfl
    obtain ⟨r, hr⟩ := ih
    refine ⟨q.append r, ?_⟩
    simp only [walkWeight_append, walkWeight_cons]
    nlinarith

theorem split_at_edge {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ (u v : V) (h : G.Adj u v) (l : G.Walk a u) (r : G.Walk v b),
      e = s(u,v) ∧ p = l.append (.cons h r) := by
  induction p with
  | nil => simp at he
  | @cons a z b haz p ih =>
    rcases List.mem_cons.mp he with he | he
    · exact ⟨a,z,haz,.nil,p,he,rfl⟩
    · obtain ⟨u,v,h,l,r,he,hl⟩ := ih he
      exact ⟨u,v,h,.cons haz l,r,he,by rw [hl]; rfl⟩

/-- Delete a specified edge of a cycle. The complementary walk has exactly
the remaining weight and uses only the other edges of that cycle. -/
theorem cycle_complement {G : SimpleGraph V} {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) (w : Sym2 V → ℝ) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ u v, e = s(u,v) ∧ ∃ q : G.Walk v u,
      walkWeight w q + w e = walkWeight w p ∧
      (∀ d ∈ q.edges, d ∈ p.edges ∧ d ≠ e) := by
  obtain ⟨u,v,h,l,r,rfl,rfl⟩ := split_at_edge p he
  refine ⟨u,v,rfl,r.append l, ?_, ?_⟩
  · simp only [walkWeight_append, walkWeight_cons]; ring
  · intro d hd
    have hnd := hp.isTrail.edges_nodup
    simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hnd
    simp only [Walk.edges_append, List.mem_append] at hd
    rcases hd with hd | hd
    · exact ⟨by simp [hd], fun he => hnd.2.1.1 (he ▸ hd)⟩
    · exact ⟨by simp [hd], fun he => hnd.2.2 d hd s(u,v) (by simp) he⟩
end LightSpanners
