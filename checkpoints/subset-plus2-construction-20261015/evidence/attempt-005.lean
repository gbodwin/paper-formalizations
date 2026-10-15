import SlackSparsification.SubsetPlusTwoPacking
import SlackSparsification.PathEdges

namespace SlackSparsification.SubsetPlusTwo
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Star and intra-cluster edges cost at most d² per cluster. Residual edges
cost at most nd. Neither bound requires a nonempty vertex type. -/
theorem clusteringCertificate_exists (G : SimpleGraph V) (d : ℕ) (hd : 0 < d) :
    Nonempty (ClusteringCertificate G d) := by
  obtain ⟨P⟩ := exists_starPacking G d hd
  let Cs := P.clusters
  let U := Cs.biUnion id
  have hcount : Cs.card * d ≤ Fintype.card V := by
    calc
      _ = ∑ C ∈ Cs, C.card := by rw [sum_congr rfl (fun C hC => P.size C hC)]; simp [Cs]
      _ = U.card := (card_biUnion (by
        intro C hC D hD hne
        exact P.disjoint C hC D hD hne)).symm
      _ ≤ Fintype.card V := card_le_univ _
  have centers : ∀ C : {C // C ∈ Cs}, ∃ c, ∀ v ∈ C.val, G.Adj v c :=
    fun C => P.star C.val C.property
  choose center hcenter using centers
  let F := fun C : {C // C ∈ Cs} => C.val.biUnion fun v =>
    ((insert (center C) (C.val.erase v)).filter (G.Adj v)).image fun w => s(v,w)
  have hFsub (C : {C // C ∈ Cs}) : F C ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v, _, he⟩ := mem_biUnion.mp he
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    simpa using (mem_filter.mp hw).2
  have hFcard (C : {C // C ∈ Cs}) : (F C).card ≤ d * d := by
    calc
      _ ≤ ∑ v ∈ C.val, (((insert (center C) (C.val.erase v)).filter (G.Adj v)).image fun w => s(v,w)).card := card_biUnion_le
      _ ≤ ∑ _v ∈ C.val, d := by
        apply sum_le_sum
        intro v hv
        apply card_image_le.trans
        apply (card_filter_le _ _).trans
        have h1 := card_insert_le (center C) (C.val.erase v)
        have h2 := card_erase_add_one hv
        have h3 := P.size C.val C.property
        omega
      _ = d * d := by simp [P.size C.val C.property]
  let A := univ.biUnion F
  let R := fun c => G.neighborFinset c \ U
  let B := univ.biUnion fun c => (R c).image fun v => s(c,v)
  have hAsub : A ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨C, _, he⟩ := mem_biUnion.mp he
    exact hFsub C he
  have hBsub : B ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨c, _, he⟩ := mem_biUnion.mp he
    obtain ⟨v, hv, rfl⟩ := mem_image.mp he
    simpa using (mem_sdiff.mp hv).1
  have hAcard : A.card ≤ Cs.card * (d * d) := by
    calc
      _ ≤ ∑ C, (F C).card := card_biUnion_le
      _ ≤ ∑ _C : {C // C ∈ Cs}, d * d := sum_le_sum fun C _ => hFcard C
      _ = _ := by simp
  have hBcard : B.card ≤ Fintype.card V * d := by
    calc
      _ ≤ ∑ c : V, ((R c).image fun v => s(c,v)).card := card_biUnion_le
      _ ≤ ∑ _c : V, d := sum_le_sum fun c _ => card_image_le.trans (P.residual c).le
      _ = _ := by simp
  let H := graphOfEdges (A ∪ B)
  have hHG : H ≤ G := graphOfEdges_le (union_subset hAsub hBsub)
  have hstar (C : {C // C ∈ Cs}) (v : V) (hv : v ∈ C.val) : H.Adj v (center C) := by
    refine ⟨mem_union_left _ (mem_biUnion.mpr ⟨C, mem_univ _, ?_⟩), (hcenter C v hv).ne⟩
    exact mem_biUnion.mpr ⟨v, hv, mem_image.mpr ⟨center C,
      mem_filter.mpr ⟨mem_insert_self _ _, hcenter C v hv⟩, rfl⟩⟩
  have hintra (C : Finset V) (hC : C ∈ Cs) (a : V) (ha : a ∈ C)
      (b : V) (hb : b ∈ C) (hab : G.Adj a b) : H.Adj a b := by
    refine ⟨mem_union_left _ (mem_biUnion.mpr ⟨⟨C, hC⟩, mem_univ _, ?_⟩), hab.ne⟩
    exact mem_biUnion.mpr ⟨a, ha, mem_image.mpr ⟨b,
      mem_filter.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨hab.ne.symm, hb⟩), hab⟩, rfl⟩⟩
  have hres (a b : V) (hab : G.Adj a b) (hb : b ∉ U) : H.Adj a b := by
    refine ⟨mem_union_right _ (mem_biUnion.mpr ⟨a, mem_univ _, ?_⟩), hab.ne⟩
    exact mem_image.mpr ⟨b, mem_sdiff.mpr ⟨by simpa using hab, hb⟩, rfl⟩
  refine ⟨⟨H, hHG, Cs, P.disjoint, P.size, ?_, hintra, ?_, hcount, ?_⟩⟩
  · intro C hC
    exact star_cluster_diameter H C (center ⟨C, hC⟩) (hstar ⟨C, hC⟩)
  · intro a b hab hmissing
    have haU : a ∈ U := by by_contra ha; exact hmissing (hres b a hab.symm ha).symm
    have hbU : b ∈ U := by by_contra hb; exact hmissing (hres a b hab hb)
    obtain ⟨C, hC, ha⟩ := mem_biUnion.mp haU
    obtain ⟨D, hD, hb⟩ := mem_biUnion.mp hbU
    refine ⟨C, hC, D, hD, ha, hb, ?_⟩
    rintro rfl
    exact hmissing (hintra C hC a ha b hb hab)
  · calc
      _ ≤ (A ∪ B).card := graphOfEdges_card_le _
      _ ≤ A.card + B.card := card_union_le _ _
      _ ≤ Cs.card * (d * d) + Fintype.card V * d := Nat.add_le_add hAcard hBcard
      _ ≤ 2 * Fintype.card V * d := by
        have := Nat.mul_le_mul_right d hcount
        nlinarith

end SlackSparsification.SubsetPlusTwo
