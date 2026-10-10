import GreedyShortcuts.CanonicalSuffixPath

/-! Suffix position incidence is exactly path incidence, because all canonical
paths are simple. This connects window degree to the heavy/light intersection sums. -/
namespace GreedyShortcuts.SuffixIncidence

open Finset DirectedPaths SuffixWindowPath
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

def vertices {s t : V} (p : DWalk s t) : Finset V :=
  (Finset.range (suffixSize p)).image (fun j => p.getVert (suffixOffset p+j))

theorem index_bound {s t : V} (p : DWalk s t) {j : ℕ} (hj : j < suffixSize p) :
    suffixOffset p+j ≤ p.length := by
  have hm : suffixSize p ≤ p.length+1 := by dsimp [suffixSize]; omega
  dsimp [suffixOffset]
  omega

theorem vertices_subset_support {s t : V} (p : DWalk s t) :
    vertices p ⊆ p.support.toFinset := by
  intro v hv
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
  exact List.mem_toFinset.mpr (p.getVert_mem_support _)

theorem vertices_card {s t : V} {p : DWalk s t} (hp : p.IsPath) :
    (vertices p).card = suffixSize p := by
  rw [vertices,Finset.card_image_iff.mpr ?_,Finset.card_range]
  intro i hi j hj he
  have hh := hp.getVert_injOn (index_bound p (Finset.mem_range.mp hi))
    (index_bound p (Finset.mem_range.mp hj)) he
  omega

theorem degree_eq_paths {s t : I → V} (p : ∀ i,DWalk (s i) (t i))
    (hp : ∀ i,(p i).IsPath) (v : V) :
    FamilyWindows.deg (fun i => suffixSize (p i))
      (fun i j => (p i).getVert (suffixOffset (p i)+j)) v =
      ((Finset.univ : Finset I).filter (fun i => v ∈ vertices (p i))).card := by
  classical
  unfold FamilyWindows.deg FiniteWindows.degree
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    have hv := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨x.2.val,Finset.mem_range.mpr x.2.isLt,?_⟩⟩
    exact hv
  · intro x hx y hy he
    rcases x with ⟨i,j⟩
    rcases y with ⟨k,l⟩
    change i = k at he
    subst k
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    change (p i).getVert (suffixOffset (p i)+j.val) = v at hx'
    change (p i).getVert (suffixOffset (p i)+l.val) = v at hy'
    have hjl := (hp i).getVert_injOn (index_bound (p i) j.isLt) (index_bound (p i) l.isLt)
      (hx'.trans hy'.symm)
    have heq : j = l := Fin.ext (by omega)
    subst l
    rfl
  · intro i hi
    obtain ⟨j,hj,hjv⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hi).2
    refine ⟨⟨i,⟨j,Finset.mem_range.mp hj⟩⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjv⟩

/-- Exact conversion of base-path suffix degree to the sum of intersection
sizes contributed by individual active paths. -/
theorem degree_sum_intersections {s t : I → V} (p : ∀ i,DWalk (s i) (t i))
    (hp : ∀ i,(p i).IsPath) (R : Finset V) :
    (∑ v ∈ R,FamilyWindows.deg (fun i => suffixSize (p i))
      (fun i j => (p i).getVert (suffixOffset (p i)+j)) v) =
      ∑ i,(R ∩ vertices (p i)).card := by
  classical
  simp_rw [degree_eq_paths p hp,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.filter_mem_eq_inter]
  simp only [Finset.sum_filter]

end GreedyShortcuts.SuffixIncidence
