import GreedyShortcuts.SuffixIncidence

/-! Exact first-quarter incidence counting for a finite active-path family. -/
namespace GreedyShortcuts.PrefixIncidence

open Finset SimpleGraph DirectedPaths SuffixWindowPath
variable {I V : Type*} [DecidableEq I] [Fintype V] [DecidableEq V]

def vertices {s t : V} (p : DWalk s t) : Finset V :=
  (Finset.range (suffixSize p)).image p.getVert

theorem mem_vertices {s t : V} {p : DWalk s t} {v : V} :
    v ∈ vertices p ↔ ∃ a < suffixSize p,p.getVert a = v := by
  simp only [vertices,Finset.mem_image,Finset.mem_range]

theorem vertices_card {s t : V} {p : DWalk s t} (hp : p.IsPath) :
    (vertices p).card = suffixSize p := by
  rw [vertices,Finset.card_image_iff.mpr ?_,Finset.card_range]
  intro i hi j hj he
  have hs : suffixSize p ≤ p.length+1 := by dsimp [suffixSize]; omega
  have hi' : i < suffixSize p := Finset.mem_range.mp hi
  have hj' : j < suffixSize p := Finset.mem_range.mp hj
  have hiL : i ≤ p.length := by omega
  have hjL : j ≤ p.length := by omega
  exact hp.getVert_injOn hiL hjL he

def family {s t : I → V} (Q : Finset I) (p : ∀ d,DWalk (s d) (t d)) (u : V) : Finset I :=
  Q.filter (fun d => u ∈ vertices (p d))

theorem sum_family {s t : I → V} (Q : Finset I) (p : ∀ d,DWalk (s d) (t d)) :
    (∑ u,(family Q p u).card) = ∑ d ∈ Q,(vertices (p d)).card := by
  simp_rw [family,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp

/-- A real vertex occurs in many first quarters; the rounding is uniform for
all path lengths exceeding the target. -/
theorem exists_vertex {s t : I → V} (Q : Finset I) (hQ : Q.Nonempty)
    (p : ∀ d,DWalk (s d) (t d)) (hp : ∀ d ∈ Q,(p d).IsPath)
    (β : ℕ) (hβ : 8 ≤ β) (hL : ∀ d ∈ Q,β < (p d).length) :
    ∃ u : V, β*Q.card ≤ 8*Fintype.card V*(family Q p u).card := by
  classical
  obtain ⟨d,hd⟩ := hQ
  haveI : Nonempty V := ⟨s d⟩
  obtain ⟨u,hu,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (fun u => (family Q p u).card) Finset.univ_nonempty
  refine ⟨u,?_⟩
  have hround : ∀ d ∈ Q,β ≤ 8*(vertices (p d)).card := by
    intro d hd
    rw [vertices_card (hp d hd)]
    have hh := hL d hd
    dsimp [suffixSize]
    omega
  calc
    β*Q.card = ∑ _d ∈ Q,β := by simp [Nat.mul_comm]
    _ ≤ ∑ d ∈ Q,8*(vertices (p d)).card := Finset.sum_le_sum hround
    _ = 8*∑ u,(family Q p u).card := by rw [← Finset.mul_sum,sum_family]
    _ ≤ 8*∑ _v : V,(family Q p u).card := Nat.mul_le_mul_left 8 (Finset.sum_le_sum hmax)
    _ = _ := by simp [Nat.mul_assoc]

end GreedyShortcuts.PrefixIncidence
