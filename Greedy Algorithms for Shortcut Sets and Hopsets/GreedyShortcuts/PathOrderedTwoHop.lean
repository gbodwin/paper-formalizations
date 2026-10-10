import GreedyShortcuts.PathMedianWitness
import Mathlib.Data.Finset.Sort

/-! Median networks on a deduplicated ordered subset retain two literal
forward legs. This stronger bound is used before adding two block connectors. -/
namespace GreedyShortcuts.PathMedian
open Finset

def orderedEdges (E : Finset ℕ) (d : ℕ) : Finset (ℕ × ℕ) :=
  (finEdges d E.card).image (fun e => (E.orderEmbOfFin rfl e.1,E.orderEmbOfFin rfl e.2))

theorem orderedEdges_card (E : Finset ℕ) (d : ℕ) :
    (orderedEdges E d).card ≤ E.card*d :=
  Finset.card_image_le.trans (finEdges_card d E.card)

theorem orderedEdges_forward {E : Finset ℕ} {d : ℕ} {e : ℕ × ℕ}
    (he : e∈orderedEdges E d) : e.1 < e.2 ∧ e.1∈E ∧ e.2∈E := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  exact ⟨(E.orderEmbOfFin rfl).strictMono (finEdges_forward d E.card hq),
    E.orderEmbOfFin_mem rfl q.1,E.orderEmbOfFin_mem rfl q.2⟩

/-- Arbitrary retained endpoints have an actual two-edge-or-fewer route
inside their ordered median network. No four-hop interface is substituted. -/
theorem ordered_two_legs (E : Finset ℕ) (d : ℕ) (hsize : E.card ≤ 2^d)
    {s t : ℕ} (hs : s∈E) (ht : t∈E) (hst : s ≤ t) :
    ∃ z,z∈E ∧ s ≤ z ∧ z ≤ t ∧ (s=z ∨ (s,z)∈orderedEdges E d) ∧
      (z=t ∨ (z,t)∈orderedEdges E d) := by
  have hs' : s∈Set.range (E.orderEmbOfFin rfl) := by
    rw [E.range_orderEmbOfFin rfl];exact hs
  have ht' : t∈Set.range (E.orderEmbOfFin rfl) := by
    rw [E.range_orderEmbOfFin rfl];exact ht
  obtain ⟨i,rfl⟩ := hs'
  obtain ⟨j,rfl⟩ := ht'
  have hij : i ≤ j := (E.orderEmbOfFin rfl).le_iff_le.mp hst
  obtain ⟨z,hiz,hzj,hizE,hzjE⟩ := two_legs d E.card i.val j.val hsize hij j.isLt
  let zz : Fin E.card := ⟨z,lt_of_le_of_lt hzj j.isLt⟩
  refine ⟨E.orderEmbOfFin rfl zz,E.orderEmbOfFin_mem rfl zz,
    (E.orderEmbOfFin rfl).monotone hiz,(E.orderEmbOfFin rfl).monotone hzj,?_,?_⟩
  · rcases hizE with he | he
    · exact Or.inl (congrArg (E.orderEmbOfFin rfl) (Fin.ext he))
    · right
      exact Finset.mem_image.mpr ⟨(i,zz),Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
  · rcases hzjE with he | he
    · exact Or.inl (congrArg (E.orderEmbOfFin rfl) (Fin.ext he))
    · right
      exact Finset.mem_image.mpr ⟨(zz,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩

end GreedyShortcuts.PathMedian
