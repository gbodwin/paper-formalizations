import LightEFTSpanners.NativeForestCardinality
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace LightEFTSpanners.MultigraphCuts
open Finset SimpleGraph
variable {V E : Type*} [Fintype E]
attribute [local instance] Classical.propDecidable

/-- Actual original identities joining two different blocks of a partition of
actual vertices. Loops never cross, while distinct parallel identities do. -/
noncomputable def actualPartitionCrossings (G : Graph V E) {I : Type*}
    (label : G.vertexSet → I) : Finset E :=
  univ.filter (fun e => ∃ a b : G.vertexSet,
    G.IsLink e a.val b.val ∧ label a≠label b)

/-- The finite spanning-tree partition criterion, with all blocks nonempty.
Labels use actual vertices rather than an unoccupied ambient vertex type. -/
def TreePartitionCriterion (G : Graph V E) (k : ℕ) : Prop :=
  ∀ (m : ℕ) (label : G.vertexSet → Fin m),Function.Surjective label →
    k*(m-1)≤(actualPartitionCrossings G label).card

/-- A genuine vertex cut is exactly the crossing set of its two-side labeling. -/
theorem two_side_crossings (G : Graph V E) (S : Set V) :
    actualPartitionCrossings G (fun a : G.vertexSet => (if a.val∈S then 0 else 1 : Fin 2))=
      (G.edgeCut S).toFinset := by
  classical
  ext e
  simp only [actualPartitionCrossings,mem_filter,mem_univ,true_and,Set.mem_toFinset]
  constructor
  · rintro ⟨a,b,he,hn⟩
    by_cases ha : a.val∈S <;> by_cases hb : b.val∈S
    · simp [ha,hb] at hn
    · exact ⟨a.val,b.val,he,ha,hb⟩
    · exact ⟨b.val,a.val,he.symm,hb,ha⟩
    · simp [ha,hb] at hn
  · rintro ⟨a,b,he,ha,hb⟩
    refine ⟨⟨a,he.left_mem⟩,⟨b,he.right_mem⟩,he,?_⟩
    simp [ha,hb]

/-- Every nontrivial actual separating cut is among the required partitions. -/
theorem partitionCriterion_faultConnected (G : Graph V E) {k : ℕ}
    (h : TreePartitionCriterion G k) (a b : G.vertexSet) : FaultConnected G k a b := by
  apply faultConnected_of_cut_lower
  intro S ha hb
  let label : G.vertexSet → Fin 2 := fun v => if v.val∈S then 0 else 1
  have hsurj : Function.Surjective label := by
    intro i
    fin_cases i
    · exact ⟨a,by simp [label,ha]⟩
    · exact ⟨b,by simp [label,hb]⟩
  have hcount := h 2 label hsurj
  simpa only [show label=(fun v : G.vertexSet => (if v.val∈S then 0 else 1 : Fin 2)) from rfl,
    two_side_crossings,Nat.reduceSub,Nat.mul_one] using hcount

/-- The positive partition criterion gives actual native connectedness when
there is at least one actual vertex. -/
theorem partitionCriterion_connected (G : Graph V E) [Nonempty G.vertexSet] {k : ℕ}
    (hk : 0<k) (h : TreePartitionCriterion G k) : G.toSimpleGraph.Connected := by
  refine ⟨?_⟩
  intro a b
  have hr := partitionCriterion_faultConnected G h a b ∅ (by simpa using hk)
  apply hr.mono
  intro u v huv
  obtain ⟨hne,e,he,_⟩ := huv
  exact ⟨hne,e,he⟩

/-- The one-tree sufficiency case of the finite partition theorem constructs
an actual spanning tree of original edge identities, including its exact size.
This is the base case only, not the general k-tree packing theorem. -/
theorem partitionCriterion_one_tree (G : Graph V E) [Nonempty G.vertexSet]
    [Finite G.vertexSet] (h : TreePartitionCriterion G 1) :
    ∃ F : Set E,F⊆G.edgeSet ∧
      (∀ e∈(G.restrict F).edgeSet,(G.restrict F).IsBridge e) ∧
      (G.restrict F).toSimpleGraph.Connected ∧
      Nat.card F+1=Nat.card G.vertexSet :=
  exists_native_spanning_tree G (partitionCriterion_connected G (by omega) h)
end LightEFTSpanners.MultigraphCuts
