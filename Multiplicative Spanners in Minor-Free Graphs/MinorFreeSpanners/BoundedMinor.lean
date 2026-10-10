import MinorFreeSpanners.MinorComposition
import MinorFreeSpanners.MinorRestriction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Actual bounded-minor composition and dense-subgraph pullback, preparing
  the graph constructions in Postle's density-increment theorem. No density
  increment or clique-density theorem is assumed here. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
namespace MinorModel
variable {I V W : Type*} {F : SimpleGraph I} {G : SimpleGraph V} {H : SimpleGraph W}
variable [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Every actual branch set has at most m vertices. -/
def IsBounded (M : MinorModel F G) (m : ℕ) : Prop :=
  ∀ i, (M.branch i).toFinset.card ≤ m

/-- Boundedness multiplies under the already constructed genuine minor
composition. This counts actual branch unions, not formal contraction labels. -/
theorem IsBounded.comp [Fintype W] (M : MinorModel F G) (N : MinorModel G H)
    {m n : ℕ} (hM : M.IsBounded m) (hN : N.IsBounded n) :
    (M.comp N).IsBounded (m*n) := by
  classical
  intro i
  have he : ((M.comp N).branch i).toFinset =
      (M.branch i).toFinset.biUnion (fun v => (N.branch v).toFinset) := by
    ext w
    rw [Set.mem_toFinset]
    simp only [Finset.mem_biUnion,Set.mem_toFinset]
    rfl
  rw [he]
  exact (card_biUnion_le_card_mul _ _ n (fun v hv => hN v)).trans
    (Nat.mul_le_mul_right n (hM i))

/-- Restrict the target to actual selected vertices, retaining the same
host branch sets and their internal walks. -/
noncomputable def induceTarget (M : MinorModel F G) (S : Set I) :
    MinorModel (F.induce S) G where
  branch := fun i => M.branch i.val
  nonempty := fun i => M.nonempty i.val
  disjoint := fun i j hij => M.disjoint i.val j.val (fun h => hij (Subtype.ext h))
  connected := fun i => M.connected i.val
  adjacent := fun i j hij => M.adjacent i.val j.val hij

theorem IsBounded.induceTarget (M : MinorModel F G) {m : ℕ}
    (hM : M.IsBounded m) (S : Set I) : (M.induceTarget S).IsBounded m :=
  fun i => hM i.val

/-- Pull a bounded minor back to an actual induced subgraph of its host,
retaining every model edge and at most m times as many vertices. -/
theorem IsBounded.exists_host_subgraph [Fintype I] [DecidableEq I] [DecidableEq V]
    [DecidableRel F.Adj] [DecidableRel G.Adj]
    (M : MinorModel F G) {m : ℕ} (hM : M.IsBounded m) :
    ∃ S : Finset V, S.card ≤ m*Fintype.card I ∧
      F.edgeFinset.card ≤ (G.induce (S:Set V)).edgeFinset.card := by
  classical
  let S := Finset.univ.biUnion (fun i => (M.branch i).toFinset)
  have hs : S.card ≤ m*Fintype.card I := by
    have hb := card_biUnion_le_card_mul (Finset.univ : Finset I)
      (fun i => (M.branch i).toFinset) m (fun i hi => hM i)
    simpa only [Finset.card_univ,Nat.mul_comm] using hb
  have hbranch : ∀ i, M.branch i ⊆ (S:Set V) := by
    intro i v hv
    simp only [S,Finset.mem_coe,Finset.mem_biUnion,Finset.mem_univ,Set.mem_toFinset,true_and]
    exact ⟨i,hv⟩
  exact ⟨S,hs,(M.induce (S:Set V) hbranch).edge_count_le⟩

end MinorModel
end MinorFreeSpanners
