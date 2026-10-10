import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Actual undirected graph walks and length-increase cuts. The zero cut is
allowed as a decomposition, including for already-expanding and empty graphs. -/
namespace LengthExpander
open SimpleGraph
variable {V : Type*}

abbrev EdgeLength (V : Type*) := Sym2 V → ℝ

def walkLength (w : EdgeLength V) {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : ℝ := (p.edges.map w).sum

@[simp] theorem walkLength_nil (w : EdgeLength V) (G : SimpleGraph V) (u : V) :
    walkLength w (.nil : G.Walk u u) = 0 := by simp [walkLength]

@[simp] theorem walkLength_cons (w : EdgeLength V) {G : SimpleGraph V}
    {u v z : V} (h : G.Adj u v) (p : G.Walk v z) :
    walkLength w (.cons h p) = w s(u,v) + walkLength w p := by simp [walkLength]

@[simp] theorem walkLength_append (w : EdgeLength V) {G : SimpleGraph V}
    {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    walkLength w (p.append q) = walkLength w p + walkLength w q := by simp [walkLength]

@[simp] theorem walkLength_reverse (w : EdgeLength V) {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) : walkLength w p.reverse = walkLength w p := by
  simp [walkLength]

theorem walkLength_mono {w w' : EdgeLength V} (h : ∀ e, w e ≤ w' e)
    {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    walkLength w p ≤ walkLength w' p := by
  induction p with
  | nil => simp
  | @cons u v z huv p ih => simpa using add_le_add (h s(u,v)) ih

/-- Distance-at-most-h in finite nonnegative weighted graphs, formulated by
an actual witnessing walk rather than division or an infinity convention. -/
def Near (G : SimpleGraph V) (w : EdgeLength V) (h : ℝ) (u v : V) : Prop :=
  ∃ p : G.Walk u v, walkLength w p ≤ h

/-- Strict separation: every connecting walk is longer than the threshold.
Disconnected pairs satisfy this predicate, as required. -/
def Far (G : SimpleGraph V) (w : EdgeLength V) (h : ℝ) (u v : V) : Prop :=
  ∀ p : G.Walk u v, h < walkLength w p

theorem far_iff_not_near {G : SimpleGraph V} {w : EdgeLength V}
    {h : ℝ} {u v : V} : Far G w h u v ↔ ¬ Near G w h u v := by
  simp [Far, Near]

theorem near_symm {G : SimpleGraph V} {w : EdgeLength V}
    {h : ℝ} {u v : V} (H : Near G w h u v) : Near G w h v u := by
  obtain ⟨p, hp⟩ := H
  exact ⟨p.reverse, by simpa using hp⟩

theorem near_triangle {G : SimpleGraph V} {w : EdgeLength V}
    {a b : ℝ} {u v z : V} (H : Near G w a u v) (K : Near G w b v z) :
    Near G w (a + b) u z := by
  obtain ⟨p, hp⟩ := H
  obtain ⟨q, hq⟩ := K
  exact ⟨p.append q, by simpa using add_le_add hp hq⟩

theorem near_length_mono {G : SimpleGraph V} {w w' : EdgeLength V}
    (hw : ∀ e, w e ≤ w' e) {h : ℝ} {u v : V}
    (H : Near G w' h u v) : Near G w h u v := by
  obtain ⟨p, hp⟩ := H
  exact ⟨p, (walkLength_mono hw p).trans hp⟩

def applyCut (w C : EdgeLength V) (h : ℝ) : EdgeLength V := fun e => w e + h * C e

theorem le_applyCut (w C : EdgeLength V) {h : ℝ}
    (hh : 0 ≤ h) (hC : ∀ e, 0 ≤ C e) : ∀ e, w e ≤ applyCut w C h e := by
  intro e
  exact le_add_of_nonneg_right (mul_nonneg hh (hC e))

@[simp] theorem applyCut_zero (w : EdgeLength V) (h : ℝ) :
    applyCut w (fun _ => 0) h = w := by funext e; simp [applyCut]

theorem applyCut_add (w C D : EdgeLength V) (h : ℝ) :
    applyCut (applyCut w C h) D h = applyCut w (fun e => C e + D e) h := by
  funext e
  simp only [applyCut]
  ring

/-- The strict triangle step in Appendix A, preserving > rather than ≥. -/
theorem dispersed_pair_far {G : SimpleGraph V} {w : EdgeLength V}
    {h s : ℝ} {u v z : V} (H : Far G w (h*s) u v)
    (K : Near G w h v z) : Far G w (h*(s-1)) u z := by
  obtain ⟨q, hq⟩ := near_symm K
  intro p
  have hpq := H (p.append q)
  simp only [walkLength_append] at hpq
  nlinarith

/-- Exact scaling identity used when changing the cut-separation threshold. -/
theorem rescaled_cut_identity (w C : EdgeLength V) {h s : ℝ} (hs : 1 < s) :
    applyCut w (fun e => (1 + 1/(s-1))*C e) (h*(s-1)) = applyCut w C (h*s) := by
  funext e
  simp only [applyCut]
  have hne : s - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hs)
  field_simp
  <;> ring

end LengthExpander
