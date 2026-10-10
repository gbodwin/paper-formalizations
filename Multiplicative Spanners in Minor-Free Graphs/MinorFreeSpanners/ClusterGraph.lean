import MinorFreeSpanners.IntrinsicGirthGap
import MinorFreeSpanners.MinorComposition

/-! The graph-theoretic part of Claim 22, for an explicitly supplied family
of disjoint low-diameter connected clusters. Hierarchy existence and the
charging argument are not assumed to be consequences of this module. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners
variable {I V : Type*}

structure ClusterFamily (A : SimpleGraph V) (w : Sym2 V → ℝ) (D : ℝ) where
  branch : I → Set V
  nonempty : ∀ i, (branch i).Nonempty
  disjoint : ∀ i j, i ≠ j → Disjoint (branch i) (branch j)
  connected : ∀ i x, x ∈ branch i → ∀ y, y ∈ branch i →
    ∃ p : A.Walk x y, (∀ z ∈ p.support, z ∈ branch i) ∧ walkWeight w p ≤ D

namespace ClusterFamily
variable {A G B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

def graph (C : ClusterFamily (I := I) A w D) (B : SimpleGraph V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ x ∈ C.branch i, ∃ y ∈ C.branch j, B.Adj x y
  symm := ⟨by rintro i j ⟨hne,x,hx,y,hy,hxy⟩; exact ⟨hne.symm,y,hy,x,hx,hxy.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Explicit cluster contraction gives a genuine branch-set minor. -/
def minorModel (C : ClusterFamily (I := I) A w D) (hA : A ≤ G) (hB : B ≤ G) :
    MinorModel (C.graph B) G where
  branch := C.branch
  nonempty := C.nonempty
  disjoint := C.disjoint
  connected := by
    intro i x hx y hy
    obtain ⟨p,hp,_⟩ := C.connected i x hx y hy
    exact ⟨p.mapLe hA,by simpa using hp⟩
  adjacent := by
    rintro i j ⟨_,x,hx,y,hy,hxy⟩
    exact ⟨x,hx,y,hy,hB hxy⟩

theorem minorFree (C : ClusterFamily (I := I) A w D) (hA : A ≤ G) (hB : B ≤ G)
    {h : ℕ} (hG : CliqueMinorFree G h) : CliqueMinorFree (C.graph B) h :=
  hG.of_minor (C.minorModel hA hB)

/-- A walk confined to strictly lighter edges avoids any given heavy edge. -/
theorem heavy_edge_not_mem {L : ℝ} (hA : ∀ e ∈ A.edgeSet, w e < L)
    {e : Sym2 V} (he : L ≤ w e) {x y : V} (p : A.Walk x y) : e ∉ p.edges := by
  intro hp
  exact (not_lt_of_ge he) (hA e (p.edges_subset_edgeSet hp))

/-- Internal cluster edges cannot appear at the heavier level when the
intrinsic girth gap exceeds the cluster diameter. -/
theorem no_heavy_loop [DecidableEq V] (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) {g L : ℝ} (hG : WeightedGirthAbove G w g)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (hlight : ∀ e ∈ A.edgeSet, w e < L)
    (hg : 1 ≤ g) (hbudget : D ≤ (g-1)*L)
    (i : I) {x y : V} (hx : x ∈ C.branch i) (hy : y ∈ C.branch i)
    (hxy : G.Adj x y) (hheavy : L ≤ w s(x,y)) : False := by
  obtain ⟨p,_,hp⟩ := C.connected i x hx y hy
  have hnot : s(x,y) ∉ (p.mapLe hA).edges := by
    simpa using heavy_edge_not_mem hlight hheavy p
  have hgap := replacement_walk_gap hG hw hxy (p.mapLe hA) hnot
  simp only [walkWeight_mapLe] at hgap
  have := mul_le_mul_of_nonneg_left hheavy (sub_nonneg.mpr hg)
  linarith

/-- Two distinct heavy edges between the same pair of clusters would form
an alternative walk contradicting weighted girth. Equal weights are allowed. -/
theorem heavy_edge_unique [DecidableEq V] (C : ClusterFamily (I := I) A w D)
    (hA : A ≤ G) {g L : ℝ} (hG : WeightedGirthAbove G w g)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (hlight : ∀ e ∈ A.edgeSet, w e < L)
    (hg : 2 ≤ g) (hbudget : 2*D ≤ (g-2)*L)
    (i j : I) {u v x y : V} (hu : u ∈ C.branch i) (hv : v ∈ C.branch j)
    (hx : x ∈ C.branch i) (hy : y ∈ C.branch j)
    (huv : G.Adj u v) (hxy : G.Adj x y)
    (hheavy : L ≤ w s(x,y)) (horder : w s(u,v) ≤ w s(x,y)) :
    s(u,v) = s(x,y) := by
  by_contra hne
  obtain ⟨p,_,hp⟩ := C.connected i x hx u hu
  obtain ⟨q,_,hq⟩ := C.connected j v hv y hy
  let r : G.Walk x y := (p.mapLe hA).append (.cons huv (q.mapLe hA))
  have hnot : s(x,y) ∉ r.edges := by
    simp only [r,Walk.edges_append,Walk.edges_cons,Walk.edges_mapLe_eq_edges,List.mem_append,
      List.mem_cons]
    exact fun h => h.elim (heavy_edge_not_mem hlight hheavy p)
      (fun h => h.elim (fun he => hne he.symm) (heavy_edge_not_mem hlight hheavy q))
  have hgap := replacement_walk_gap hG hw hxy r hnot
  simp only [r,walkWeight_append,walkWeight_cons,walkWeight_mapLe] at hgap
  have := mul_le_mul_of_nonneg_left hheavy (sub_nonneg.mpr hg)
  nlinarith

end ClusterFamily

/-- The same s≥4c repair suffices for the no-parallel-edge budget at each
scale, using the corrected greedy girth t+1 rather than the printed value. -/
theorem cluster_parameter_budget (k : ℕ) (c s ε ℓ : ℝ)
    (hk : 1 ≤ k) (hc : 0 ≤ c) (hs : 4*c ≤ s) (he : 0 < ε) (hl : 0 ≤ ℓ) :
    2 ≤ (1+s*ε)*(2*k-1)+1 ∧
    2*(c*ℓ) ≤ ((1+s*ε)*(2*k-1)+1-2) * (ℓ/(2*ε)) := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hs' : 0 ≤ s := by linarith
  have hse := mul_le_mul_of_nonneg_right hs he.le
  have hp := mul_nonneg (mul_nonneg hs' he.le) (show 0 ≤ 2*(k:ℝ)-2 by linarith)
  have hb : 4*c*ε ≤ (1+s*ε)*(2*k-1)+1-2 := by nlinarith
  constructor
  · nlinarith [mul_nonneg hc he.le]
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ (mul_pos (by norm_num) he)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb hl]

end MinorFreeSpanners
