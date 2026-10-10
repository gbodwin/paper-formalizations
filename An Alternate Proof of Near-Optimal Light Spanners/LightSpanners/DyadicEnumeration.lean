import LightSpanners.UnitCycleWeight
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Combinatorics.SimpleGraph.Dart

namespace LightSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] [Fintype V]

namespace UnitSpanningCycle
variable {G : SimpleGraph V} {w : Sym2 V → ℝ} (C : UnitSpanningCycle G w)

/-- Removing the actual Hamiltonian unit cycle removes exactly `card V` weight. -/
theorem noncycle_weight :
    ∑ e ∈ G.edgeFinset with e ∉ C.cycle.edges, w e =
      totalWeight G w - (Fintype.card V : ℝ) := by
  classical
  have hcycle : G.edgeFinset.filter (fun e => e ∈ C.cycle.edges) =
      C.cycle.edges.toFinset := by
    ext e
    simp only [Finset.mem_filter, mem_edgeFinset, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨C.cycle.edges_subset_edgeSet h, h⟩⟩
  have hweight : ∑ e ∈ G.edgeFinset with e ∈ C.cycle.edges, w e =
      (Fintype.card V : ℝ) := by
    rw [hcycle]
    calc
      _ = ∑ _e ∈ C.cycle.edges.toFinset, (1 : ℝ) :=
        Finset.sum_congr rfl (fun e he => C.unit e (List.mem_toFinset.mp he))
      _ = (Fintype.card V : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [List.toFinset_card_of_nodup C.hamiltonian.isCycle.isTrail.edges_nodup,
          Walk.length_edges, C.hamiltonian.length_eq]
  have hsplit := Finset.sum_filter_add_sum_filter_not G.edgeFinset
    (fun e => e ∈ C.cycle.edges) w
  rw [hweight] at hsplit
  exact eq_sub_of_add_eq' hsplit

omit [DecidableEq V] [Fintype V] in
/-- Every actual graph edge admits an orientation as a dart. -/
theorem exists_dart_of_edge {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ d : G.Dart, d.edge = e := by
  induction e using Sym2.inductionOn with
  | hf u v => exact ⟨⟨(u,v), (mem_edgeSet G).mp he⟩, rfl⟩

/-- A finite, actual dyadic enumeration of all non-cycle graph edges. Every
edge occurs in exactly one bucket, with no repeated undirected edge in a bucket. -/
theorem exists_finite_dyadic_buckets :
    ∃ (J : ℕ) (ds : ℕ → List G.Dart),
      (∀ i, ((ds i).map Dart.edge).Nodup) ∧
      (∀ i d, d ∈ ds i → d.edge ∉ C.cycle.edges) ∧
      (∀ i d, d ∈ ds i → (2 : ℝ)^i ≤ w d.edge ∧ w d.edge < 2^(i+1)) ∧
      (∀ e, (e ∈ G.edgeSet ∧ e ∉ C.cycle.edges) ↔
        ∃ i < J, e ∈ (ds i).map Dart.edge) ∧
      (∑ i ∈ Finset.range J, ((ds i).map (fun d => w d.edge)).sum) =
        totalWeight G w - (Fintype.card V : ℝ) := by
  classical
  let s := G.edgeFinset.filter (fun e => e ∉ C.cycle.edges)
  have hedge (e : {e // e ∈ s}) : e.val ∈ G.edgeSet :=
    mem_edgeFinset.mp (Finset.mem_filter.mp e.property).1
  choose orient horient using (fun e : {e // e ∈ s} =>
    exists_dart_of_edge (hedge e))
  choose index hindex using (fun e : {e // e ∈ s} =>
    exists_nat_pow_near (C.lower e.val (hedge e)) (by norm_num : (1 : ℝ) < 2))
  let J := s.attach.sup index + 1
  have hbound (e : {e // e ∈ s}) : index e < J := by
    exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_attach s e))
  let bucket (i : ℕ) := s.attach.filter (fun e => index e = i)
  let ds (i : ℕ) := (bucket i).toList.map orient
  have hmap (i : ℕ) : (ds i).map Dart.edge = (bucket i).toList.map Subtype.val := by
    simp only [ds, List.map_map, Function.comp_def, horient]
  have hmem (i : ℕ) (e : {e // e ∈ s}) :
      e ∈ (bucket i).toList ↔ index e = i := by
    simp [bucket]
  have hds (i : ℕ) (d : G.Dart) (hd : d ∈ ds i) :
      ∃ e : {e // e ∈ s}, index e = i ∧ orient e = d := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact ⟨e, (hmem i e).mp he, rfl⟩
  refine ⟨J, ds, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hmap]
    exact List.Nodup.map Subtype.val_injective (bucket i).nodup_toList
  · intro i d hd
    obtain ⟨e, _, rfl⟩ := hds i d hd
    rw [horient]
    exact (Finset.mem_filter.mp e.property).2
  · intro i d hd
    obtain ⟨e, hi, rfl⟩ := hds i d hd
    rw [horient, ← hi]
    exact hindex e
  · intro e
    constructor
    · rintro ⟨he, hc⟩
      have hs : e ∈ s := Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr he, hc⟩
      let a : {e // e ∈ s} := ⟨e, hs⟩
      refine ⟨index a, hbound a, ?_⟩
      rw [hmap]
      exact List.mem_map.mpr ⟨a, (hmem _ _).mpr rfl, rfl⟩
    · rintro ⟨i, _, he⟩
      rw [hmap] at he
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
      exact ⟨hedge a, (Finset.mem_filter.mp a.property).2⟩
  · have hsum (i : ℕ) : ((ds i).map (fun d => w d.edge)).sum =
        ∑ e ∈ bucket i, w e.val := by
      simp only [ds, List.map_map, Function.comp_def, horient]
      exact (List.sum_toFinset _ (bucket i).nodup_toList).symm.trans (by simp)
    simp only [hsum]
    change (∑ i ∈ Finset.range J, ∑ e ∈ s.attach with index e = i, w e.val) = _
    rw [Finset.sum_fiberwise_of_maps_to (fun e _ => Finset.mem_range.mpr (hbound e)),
      Finset.sum_attach]
    exact C.noncycle_weight

omit [DecidableEq V] [Fintype V] in
/-- Disjoint dyadic intervals force every non-cycle edge to have a unique index. -/
theorem dyadic_interval_index_unique {x : ℝ} {i j : ℕ}
    (hi : (2 : ℝ)^i ≤ x ∧ x < 2^(i+1))
    (hj : (2 : ℝ)^j ≤ x ∧ x < 2^(j+1)) : i = j := by
  have hle {a b : ℕ} (ha : (2 : ℝ)^a ≤ x)
      (hb : x < (2 : ℝ)^(b+1)) : a ≤ b := by
    by_contra h
    have hp : (2 : ℝ)^(b+1) ≤ 2^a :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  exact Nat.le_antisymm (hle hi.1 hj.2) (hle hj.1 hi.2)

end UnitSpanningCycle
end LightSpanners

