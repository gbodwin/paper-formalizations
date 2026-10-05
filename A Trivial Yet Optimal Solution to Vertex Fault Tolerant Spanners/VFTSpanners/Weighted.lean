import VFTSpanners.BlockingSet
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace VFTSpanners
open SimpleGraph
variable {V : Type*}

/-- Sum of original edge weights along a walk, counting multiplicity. -/
def walkWeight (w : Sym2 V → ℝ) {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : ℝ := (p.edges.map w).sum

@[simp] theorem walkWeight_nil (w : Sym2 V → ℝ) (G : SimpleGraph V) (u : V) :
    walkWeight w (.nil : G.Walk u u) = 0 := by simp [walkWeight]

@[simp] theorem walkWeight_cons (w : Sym2 V → ℝ) {G : SimpleGraph V}
    {u v z : V} (h : G.Adj u v) (p : G.Walk v z) :
    walkWeight w (.cons h p) = w s(u,v) + walkWeight w p := by simp [walkWeight]

/-- Walk weights are nonnegative under the main theorem's weight hypothesis. -/
theorem walkWeight_nonneg (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : 0 ≤ walkWeight w p := by
  induction p with
  | nil => simp
  | cons h p ih => simpa only [walkWeight_cons] using add_nonneg (hw _) ih

@[simp] theorem walkWeight_append (w : Sym2 V → ℝ) {G : SimpleGraph V}
    {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by
  simp [walkWeight]

@[simp] theorem walkWeight_mapLe (w : Sym2 V → ℝ) {G H : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (h : G ≤ H) :
    walkWeight w (p.mapLe h) = walkWeight w p := by simp [walkWeight]

@[simp] theorem walkWeight_transfer (w : Sym2 V → ℝ) {G H : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (h : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    walkWeight w (p.transfer H h) = walkWeight w p := by simp [walkWeight]

theorem walkWeight_le (w : Sym2 V → ℝ) {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (c : ℝ) (h : ∀ e ∈ p.edges, w e ≤ c) :
    walkWeight w p ≤ (p.length : ℝ)*c := by
  induction p with
  | nil => simp
  | @cons u v z huv p ih =>
    have hhead := h s(u,v) (by simp)
    have htail := ih (fun e he => h e (by simp [he]))
    simp only [walkWeight_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Faults are excluded at every vertex, including the two endpoints. -/
def Avoids [DecidableEq V] (F : Finset V) {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Prop := ∀ x ∈ p.support, x ∉ F

/-- The usual edge test in the fault-tolerant greedy algorithm. -/
def Covered [DecidableEq V] (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (k f : ℕ) (e : Sym2 V) : Prop :=
  ∀ u v, s(u,v) = e → ∀ F : Finset V, F.card ≤ f → u ∉ F → v ∉ F →
    ∃ p : H.Walk u v, Avoids F p ∧ walkWeight w p ≤ (k : ℝ)*w e

/-- Walk formulation of fault-tolerant stretch: every fault-avoiding input
walk has a fault-avoiding replacement of at most `k` times its weight. -/
def IsVFTSpanner [DecidableEq V] (G H : SimpleGraph V) (w : Sym2 V → ℝ)
    (k f : ℕ) : Prop := H ≤ G ∧
  ∀ F : Finset V, F.card ≤ f → ∀ u v (p : G.Walk u v), Avoids F p →
    ∃ q : H.Walk u v, Avoids F q ∧ walkWeight w q ≤ (k : ℝ)*walkWeight w p

theorem covered_mono [DecidableEq V] {H K : SimpleGraph V} (hHK : H ≤ K)
    {w : Sym2 V → ℝ} {k f : ℕ} {e : Sym2 V} (h : Covered H w k f e) :
    Covered K w k f e := by
  intro u v he F hF hu hv
  obtain ⟨p, hp, hw⟩ := h u v he F hF hu hv
  exact ⟨p.mapLe hHK, by simpa [Avoids] using hp, by simpa using hw⟩

theorem covered_of_mem [DecidableEq V] {H : SimpleGraph V} {w : Sym2 V → ℝ}
    {k f : ℕ} (hk : 1 ≤ k) (hw : ∀ e, 0 ≤ w e)
    {e : Sym2 V} (he : e ∈ H.edgeSet) : Covered H w k f e := by
  intro u v huv F hF hu hv
  have hadj : H.Adj u v := (mem_edgeSet H).mp (huv ▸ he)
  refine ⟨hadj.toWalk, ?_, ?_⟩
  · simpa [Avoids] using And.intro hu hv
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [SimpleGraph.Adj.toWalk, walkWeight_cons, walkWeight_nil, add_zero, huv]
    nlinarith [hw e]

theorem covered_edges_spanner [DecidableEq V] {G H : SimpleGraph V}
    {w : Sym2 V → ℝ} {k f : ℕ} (hHG : H ≤ G)
    (h : ∀ e ∈ G.edgeSet, Covered H w k f e) : IsVFTSpanner G H w k f := by
  refine ⟨hHG, ?_⟩
  intro F hF u v p hp
  induction p with
  | nil => exact ⟨.nil, hp, by simp⟩
  | @cons u v z huv p ih =>
    have hu : u ∉ F := hp u (by simp)
    have hv : v ∉ F := hp v (by simp [p.start_mem_support])
    obtain ⟨q, hq, hqw⟩ := h s(u,v) ((mem_edgeSet G).mpr huv) u v rfl F hF hu hv
    obtain ⟨t, ht, htw⟩ := ih (fun x hx => hp x (by simp [hx]))
    refine ⟨q.append t, ?_, ?_⟩
    · intro x hx
      simp only [Walk.mem_support_append_iff] at hx
      rcases hx with hx | hx
      · exact hq x hx
      · exact ht x hx
    · simp only [walkWeight_append, walkWeight_cons]
      nlinarith

/-- Cut a walk at a specified occurrence of an edge. -/
theorem split_at_edge {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ (u v : V) (h : G.Adj u v) (l : G.Walk a u) (r : G.Walk v b),
      e = s(u,v) ∧ p = l.append (.cons h r) := by
  induction p with
  | nil => simp at he
  | @cons a z b haz p ih =>
    rcases List.mem_cons.mp he with he | he
    · exact ⟨a,z,haz,.nil,p,he, rfl⟩
    · obtain ⟨u,v,h,l,r,he,hl⟩ := ih he
      exact ⟨u,v,h,.cons haz l,r,he,by rw [hl]; rfl⟩

/-- Removing one edge of a cycle leaves a walk between its endpoints,
using each other edge once and no new vertices. -/
theorem cycle_complement {G : SimpleGraph V} {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ u v, e = s(u,v) ∧ ∃ q : G.Walk v u,
      q.length + 1 = p.length ∧
      (∀ d ∈ q.edges, d ∈ p.edges ∧ d ≠ e) ∧
      (∀ x ∈ q.support, x ∈ p.support) := by
  obtain ⟨u,v,h,l,r,rfl,rfl⟩ := split_at_edge p he
  refine ⟨u,v,rfl,r.append l, ?_, ?_, ?_⟩
  · simp only [Walk.length_append, Walk.length_cons]; omega
  · intro d hd
    have hnd := hp.isTrail.edges_nodup
    simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hnd
    simp only [Walk.edges_append, List.mem_append] at hd
    rcases hd with hd | hd
    · exact ⟨by simp [hd], fun he => hnd.2.1.1 (he ▸ hd)⟩
    · refine ⟨by simp [hd], ?_⟩
      intro he
      exact hnd.2.2 d hd s(u,v) (by simp) he
  · intro x hx
    simp only [Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · exact (Walk.mem_support_append_iff ..).mpr (Or.inr (by simp [hx]))
    · exact (Walk.mem_support_append_iff ..).mpr (Or.inl hx)

end VFTSpanners
