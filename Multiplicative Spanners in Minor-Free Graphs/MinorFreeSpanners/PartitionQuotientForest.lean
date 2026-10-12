import MinorFreeSpanners.SaturatedForestExtension

/-! Quotient a real tree by arbitrary disjoint covering pieces. The pieces
need not be tree-connected: four-arm roots may use a heavy joining edge.
Keep every original edge between singleton residual pieces and choose a tree
inside the quotient. Thus no residual edge is lost or invented. -/
namespace MinorFreeSpanners
open SimpleGraph

structure LabelPartition (I J : Type*) where
  piece : J → Set I
  nonempty : ∀ j,(piece j).Nonempty
  disjoint : ∀ j k,j≠k → Disjoint (piece j) (piece k)
  covers : ∀ i,∃ j,i∈piece j

namespace LabelPartition
variable {I J : Type*}

noncomputable def representative (P : LabelPartition I J) (j : J) : I :=
  (P.nonempty j).choose

 theorem representative_mem (P : LabelPartition I J) (j : J) :
    P.representative j∈P.piece j := (P.nonempty j).choose_spec

 theorem label_unique (P : LabelPartition I J) {j k : J} {i : I}
    (hj : i∈P.piece j) (hk : i∈P.piece k) : j=k := by
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint j k h) hj hk

noncomputable def representativeEmbedding (P : LabelPartition I J) : J ↪ I where
  toFun := P.representative
  inj' := by
    intro j k h
    exact P.label_unique (h ▸ P.representative_mem j) (P.representative_mem k)

def graph (P : LabelPartition I J) (K : SimpleGraph I) : SimpleGraph J where
  Adj j k := j≠k ∧ ∃ x∈P.piece j,∃ y∈P.piece k,K.Adj x y
  symm := ⟨by rintro j k ⟨hne,x,hx,y,hy,hxy⟩;exact ⟨hne.symm,y,hy,x,hx,hxy.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

 theorem graph_connected (P : LabelPartition I J) {K : SimpleGraph I}
    (hK : K.Connected) : (P.graph K).Connected := by
  have : Nonempty I := hK.nonempty
  obtain ⟨j,_⟩ := P.covers (Classical.arbitrary I)
  have : Nonempty J := ⟨j⟩
  have lift {x y : I} (p : K.Walk x y) :
      ∀ j,x∈P.piece j → ∀ k,y∈P.piece k → (P.graph K).Reachable j k := by
    induction p with
    | nil =>
      intro j hj k hk
      have he := P.label_unique hj hk
      subst k
      exact .refl _
    | cons h p ih =>
      intro j hj k hk
      obtain ⟨l,hl⟩ := P.covers _
      have hlk := ih l hl k hk
      by_cases he : j=l
      · simpa [he] using hlk
      · exact (show (P.graph K).Adj j l from ⟨he,_,hj,_,hl,h⟩).reachable.trans hlk
  refine ⟨fun j k => ?_⟩
  obtain ⟨p⟩ := hK.preconnected (P.representative j) (P.representative k)
  exact lift p j (P.representative_mem j) k (P.representative_mem k)

 theorem singleton_residual_graph (P : LabelPartition I J) (K : SimpleGraph I)
    (R : Set J) (hsingle : ∀ j∈R,P.piece j={P.representative j}) :
    withinVertices (P.graph K) R=
      withinVertices (K.comap P.representativeEmbedding) R := by
  ext j k
  constructor
  · rintro ⟨⟨_,x,hx,y,hy,hxy⟩,hj,hk⟩
    rw [hsingle j hj] at hx
    rw [hsingle k hk] at hy
    have hx' : x=P.representative j := hx
    have hy' : y=P.representative k := hy
    subst x
    subst y
    exact ⟨hxy,hj,hk⟩
  · rintro ⟨hjk,hj,hk⟩
    refine ⟨⟨?_,P.representative j,P.representative_mem j,
      P.representative k,P.representative_mem k,hjk⟩,hj,hk⟩
    intro he
    subst k
    exact K.ne_of_adj hjk rfl

 theorem exists_tree_preserving_singletons (P : LabelPartition I J) (K : SimpleGraph I)
    (hK : K.IsTree) (R : Set J) (hsingle : ∀ j∈R,P.piece j={P.representative j}) :
    ∃ H : SimpleGraph J,H≤P.graph K ∧ H.IsTree ∧
      withinVertices H R=withinVertices (P.graph K) R := by
  let Q := P.graph K
  let B := withinVertices Q R
  have hBQ : B≤Q := fun _ _ h => h.1
  have hB : B.IsAcyclic := by
    rw [show B=withinVertices (K.comap P.representativeEmbedding) R from
      P.singleton_residual_graph K R hsingle]
    exact (hK.isAcyclic.of_comap P.representativeEmbedding).anti (fun _ _ h => h.1)
  obtain ⟨H,hBH,hHQ,hH⟩ := (P.graph_connected hK.connected).exists_isTree_le_of_le_of_isAcyclic hBQ hB
  refine ⟨H,hHQ,hH,?_⟩
  ext j k
  exact ⟨fun h => ⟨hHQ h.1,h.2⟩,fun h => ⟨hBH h,h.2⟩⟩

end LabelPartition
end MinorFreeSpanners
