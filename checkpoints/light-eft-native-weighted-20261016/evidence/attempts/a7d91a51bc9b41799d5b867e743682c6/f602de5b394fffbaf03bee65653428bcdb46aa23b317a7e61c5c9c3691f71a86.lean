import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

/-! Weighted edge-identified fault semantics. Vertices and edge identities are
those of the original native graph; no simplification or subdivision is used.
Weights are nonnegative finite reals, allowing zero weights and loops. -/
namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal ENNReal
variable {V E : Type*}

/-- A surviving walk records each actual traversed edge identity. -/
inductive Walk (G : Graph V E) (H F : Finset E) : G.vertexSet → G.vertexSet → Type _
  | nil (u) : Walk G H F u u
  | cons {u v z} (e : E) (link : G.IsLink e u.val v.val)
      (kept : e ∈ H) (survives : e ∉ F) (tail : Walk G H F v z) : Walk G H F u z

namespace Walk
variable {G : Graph V E} {H J F : Finset E} {u v z : G.vertexSet}

def weight (w : E → ℝ≥0) : {u v : G.vertexSet} → Walk G H F u v → ℝ≥0
  | _, _, .nil _ => 0
  | _, _, .cons e _ _ _ p => w e + weight w p

def append : {u v z : G.vertexSet} → Walk G H F u v → Walk G H F v z → Walk G H F u z
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e h he hf p, q => .cons e h he hf (append p q)

@[simp] theorem weight_append (w : E → ℝ≥0) (p : Walk G H F u v)
    (q : Walk G H F v z) : (p.append q).weight w = p.weight w + q.weight w := by
  induction p with
  | nil => simp [append, weight]
  | cons e h he hf p ih => simp [append, weight, ih, add_assoc]

def mono (h : H ⊆ J) : {u v : G.vertexSet} → Walk G H F u v → Walk G J F u v
  | _, _, .nil _ => .nil _
  | _, _, .cons e hl he hf p => .cons e hl (h he) hf (mono h p)

@[simp] theorem weight_mono (w : E → ℝ≥0) (h : H ⊆ J) (p : Walk G H F u v) :
    (p.mono h).weight w = p.weight w := by
  induction p with
  | nil => rfl
  | cons e hl he hf p ih => simp [mono, weight, ih]
end Walk

/-- The step condition is exactly native restriction followed by fault deletion. -/
theorem surviving_link_iff (G : Graph V E) (H F : Finset E) (e : E) (u v : V) :
    ((G.restrict (H : Set E)).deleteEdges (F : Set E)).IsLink e u v ↔
      G.IsLink e u v ∧ e ∈ H ∧ e ∉ F := by
  simp only [Graph.deleteEdges_isLink, Graph.restrict_isLink, mem_coe]
  tauto

/-- Infinite distance represents the absence of any surviving weighted walk. -/
noncomputable def distance (G : Graph V E) (w : E → ℝ≥0) (H F : Finset E)
    (u v : G.vertexSet) : ℝ≥0∞ := ⨅ p : Walk G H F u v, (p.weight w : ℝ≥0∞)

theorem distance_eq_top_iff (G : Graph V E) (w : E → ℝ≥0) (H F : Finset E)
    (u v : G.vertexSet) : distance G w H F u v = ⊤ ↔ ¬ Nonempty (Walk G H F u v) := by
  constructor
  · intro h ⟨p⟩
    have hp : distance G w H F u v ≤ (p.weight w : ℝ≥0∞) := iInf_le _ p
    rw [h] at hp
    exact ENNReal.coe_ne_top (top_le_iff.mp hp)
  · intro h
    let : IsEmpty (Walk G H F u v) := ⟨fun p => h ⟨p⟩⟩
    simp [distance]

/-- Walkwise EFT stretch retains witnesses, also when the original demand is
unreachable. The latter requires no replacement walk. -/
def IsEFTSpanner (G : Graph V E) (w : E → ℝ≥0) (A H : Finset E) (q : ℕ) (t : ℝ≥0) : Prop :=
  H ⊆ A ∧ ∀ F : Finset E, F.card ≤ q → ∀ u v (p : Walk G A F u v),
    ∃ r : Walk G H F u v, r.weight w ≤ t * p.weight w

/-- Replacing each surviving original edge suffices; replacements may use
other parallel identities, but cannot use a failed identity. -/
theorem edgewise_replacement (G : Graph V E) (w : E → ℝ≥0)
    (A H : Finset E) (q : ℕ) (t : ℝ≥0) (hHA : H ⊆ A)
    (h : ∀ F : Finset E, F.card ≤ q → ∀ (u v : G.vertexSet) e,
      G.IsLink e u.val v.val → e ∈ A → e ∉ F →
      ∃ r : Walk G H F u v, r.weight w ≤ t * w e) :
    IsEFTSpanner G w A H q t := by
  refine ⟨hHA, ?_⟩
  intro F hF u v p
  induction p with
  | nil u => exact ⟨.nil u, by simp [Walk.weight]⟩
  | @cons u v z e hl he hf p ih =>
    obtain ⟨r, hr⟩ := h F hF u v e hl he hf
    obtain ⟨s, hs⟩ := ih
    refine ⟨r.append s, ?_⟩
    simpa [Walk.weight, mul_add] using add_le_add hr hs

/-- The walkwise theorem gives the usual extended-distance stretch. Positive
stretch is explicit so unreachable distances are handled without 0*infinity. -/
theorem IsEFTSpanner.distance_le {G : Graph V E} {w : E → ℝ≥0}
    {A H : Finset E} {q : ℕ} {t : ℝ≥0} (h : IsEFTSpanner G w A H q t)
    (ht : t ≠ 0) (F : Finset E) (hF : F.card ≤ q) (u v : G.vertexSet) :
    distance G w H F u v ≤ (t : ℝ≥0∞) * distance G w A F u v := by
  rw [distance, distance, ENNReal.mul_iInf_of_ne (by exact_mod_cast ht) ENNReal.coe_ne_top]
  apply le_iInf
  intro p
  obtain ⟨r, hr⟩ := h.2 F hF u v p
  exact (iInf_le _ r).trans (by exact_mod_cast hr)

/-- Connectivity preservation is quantified over faults in the original ID
universe, including failures outside the chosen preserver. -/
def IsConnectivityPreserver (G : Graph V E) (A H : Finset E) (q : ℕ) : Prop :=
  H ⊆ A ∧ ∀ F : Finset E, F.card ≤ q → ∀ u v,
    Nonempty (Walk G A F u v) → Nonempty (Walk G H F u v)

theorem connectivity_iff (G : Graph V E) (A H : Finset E) (q : ℕ)
    (h : IsConnectivityPreserver G A H q) (F : Finset E) (hF : F.card ≤ q)
    (u v : G.vertexSet) : Nonempty (Walk G H F u v) ↔ Nonempty (Walk G A F u v) :=
  ⟨fun ⟨p⟩ => ⟨p.mono h.1⟩, h.2 F hF u v⟩

theorem IsEFTSpanner.connectivity {G : Graph V E} {w : E → ℝ≥0}
    {A H : Finset E} {q : ℕ} {t : ℝ≥0} (h : IsEFTSpanner G w A H q t) :
    IsConnectivityPreserver G A H q := by
  refine ⟨h.1, ?_⟩
  intro F hF u v ⟨p⟩
  obtain ⟨r, _⟩ := h.2 F hF u v p
  exact ⟨r⟩

def totalWeight (w : E → ℝ≥0) (H : Finset E) : ℝ≥0 := ∑ e ∈ H, w e

/-- Finite edge identities give an attained minimum, including empty inputs
and zero weights. No connectivity or positivity hypothesis is needed. -/
theorem exists_minimum_preserver (G : Graph V E) (w : E → ℝ≥0) (A : Finset E) (q : ℕ) :
    ∃ H, IsConnectivityPreserver G A H q ∧
      ∀ J, IsConnectivityPreserver G A J q → totalWeight w H ≤ totalWeight w J := by
  classical
  let S := A.powerset.filter fun H => IsConnectivityPreserver G A H q
  have hA : IsConnectivityPreserver G A A q := ⟨Subset.rfl, fun _ _ _ _ hp => hp⟩
  have hmem : A ∈ S := by simp [S, hA]
  obtain ⟨H, hH, hmin⟩ := S.exists_min_image (totalWeight w) ⟨A, hmem⟩
  refine ⟨H, (mem_filter.mp hH).2, ?_⟩
  intro J hJ
  exact hmin J (mem_filter.mpr ⟨mem_powerset.mpr hJ.1, hJ⟩)

noncomputable def minimumPreserverWeight (G : Graph V E) (w : E → ℝ≥0)
    (A : Finset E) (q : ℕ) : ℝ≥0 :=
  totalWeight w (exists_minimum_preserver G w A q).choose

theorem minimumPreserverWeight_attained (G : Graph V E) (w : E → ℝ≥0)
    (A : Finset E) (q : ℕ) :
    ∃ H, IsConnectivityPreserver G A H q ∧ totalWeight w H = minimumPreserverWeight G w A q ∧
      ∀ J, IsConnectivityPreserver G A J q → minimumPreserverWeight G w A q ≤ totalWeight w J := by
  obtain ⟨hH, hmin⟩ := (exists_minimum_preserver G w A q).choose_spec
  exact ⟨_, hH, rfl, hmin⟩

/-- A pair of parallel original IDs: failure of e0 leaves e1 available at its
own weight. This regression would be false if faults deleted endpoint pairs. -/
theorem parallel_identity_survives [DecidableEq E] (u v : V) (e0 e1 : E) (hne : e1 ≠ e0)
    (w : E → ℝ≥0) :
    let G := Graph.banana u v ({e0, e1} : Set E)
    ∃ p : Walk G {e0, e1} {e0} ⟨u, by simp [G]⟩ ⟨v, by simp [G]⟩,
      p.weight w = w e1 := by
  dsimp
  refine ⟨.cons e1 ⟨by simp, Or.inl ⟨rfl, rfl⟩⟩ (by simp) (by simpa using hne) (.nil _), ?_⟩
  simp [Walk.weight]

/-- The canonical original input edge set, with each parallel ID counted once. -/
noncomputable def inputEdges [Fintype E] (G : Graph V E) : Finset E := G.edgeSet.toFinset

/-- The genuine native-graph minimum is attained by a subset of actual input IDs. -/
theorem native_minimum_attained [Fintype E] (G : Graph V E) (w : E → ℝ≥0) (q : ℕ) :
    ∃ H, (∀ e ∈ H, e ∈ G.edgeSet) ∧
      IsConnectivityPreserver G (inputEdges G) H q ∧
      totalWeight w H = minimumPreserverWeight G w (inputEdges G) q ∧
      ∀ J, IsConnectivityPreserver G (inputEdges G) J q → totalWeight w H ≤ totalWeight w J := by
  obtain ⟨H, hH, heq, hmin⟩ := minimumPreserverWeight_attained G w (inputEdges G) q
  refine ⟨H, ?_, hH, heq, ?_⟩
  · intro e he
    exact Set.mem_toFinset.mp (hH.1 he)
  · intro J hJ
    rw [heq]
    exact hmin J hJ

/-- Native edgewise replacements imply EFT distance stretch on the unchanged
vertex type, after deleting the same original IDs from both input and output. -/
theorem native_edgewise_distance [Fintype E] (G : Graph V E) (w : E → ℝ≥0)
    (H : Finset E) (q : ℕ) (t : ℝ≥0) (ht : t ≠ 0) (hH : H ⊆ inputEdges G)
    (h : ∀ F : Finset E, F.card ≤ q → ∀ (u v : G.vertexSet) e,
      G.IsLink e u.val v.val → e ∉ F →
      ∃ r : Walk G H F u v, r.weight w ≤ t * w e) :
    ∀ F : Finset E, F.card ≤ q → ∀ u v,
      distance G w H F u v ≤ (t : ℝ≥0∞) * distance G w (inputEdges G) F u v := by
  have hs := edgewise_replacement G w (inputEdges G) H q t hH
    (fun F hF u v e hl _ hf => h F hF u v e hl hf)
  exact hs.distance_le ht

/-- Explicit edge-ID deletion regression: e0 is absent, while e1 still links
exactly the same original endpoints. No endpoint-pair deletion is performed. -/
theorem parallel_delete_exact [DecidableEq E] (u v : V) (e0 e1 : E) (hne : e1 ≠ e0) :
    let G := Graph.banana u v ({e0, e1} : Set E)
    ¬ (G.deleteEdges ({e0} : Finset E)).IsLink e0 u v ∧
      (G.deleteEdges ({e0} : Finset E)).IsLink e1 u v := by
  simp [Graph.deleteEdges_isLink, Graph.banana_isLink, hne]

end LightEFTSpanners.NativeWeighted
