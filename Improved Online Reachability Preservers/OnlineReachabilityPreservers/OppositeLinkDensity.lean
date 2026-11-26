import OnlineReachabilityPreservers.OppositeLinkForest
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Algebra.Field.ZMod

/-! Finite incidence graphs with many opposite links at cutoff four. -/

namespace OnlineReachabilityPreservers

open scoped List

private abbrev AffineVertex (F : Type*) := (F × F) ⊕ (F × F)

private def affineAdj (F : Type*) [Field F] : AffineVertex F → AffineVertex F → Prop
  | .inl point, .inr line => point.2 = line.1*point.1+line.2
  | .inr line, .inl point => point.2 = line.1*point.1+line.2
  | _, _ => False

private def affineGraph (F : Type*) [Field F] : SimpleGraph (AffineVertex F) where
  Adj := affineAdj F
  symm := ⟨by intro u v h; cases u <;> cases v <;> exact h⟩
  loopless := ⟨by intro u; cases u <;> simp [affineAdj]⟩

private theorem affineGraph_no_triangle {F : Type*} [Field F] {u v w : AffineVertex F}
    (uv : (affineGraph F).Adj u v) (vw : (affineGraph F).Adj v w) (wu : (affineGraph F).Adj w u) : False := by
  cases u <;> cases v <;> cases w <;> simp_all only [affineGraph,affineAdj]

private theorem line_through_two_unique {F : Type*} [Field F] {P Q L K : F × F} (apart : P ≠ Q)
    (pl : P.2 = L.1*P.1+L.2) (pk : P.2 = K.1*P.1+K.2)
    (ql : Q.2 = L.1*Q.1+L.2) (qk : Q.2 = K.1*Q.1+K.2) : L = K := by
  have abscissa : P.1 ≠ Q.1 := by
    intro eq
    apply apart
    exact Prod.ext eq (by rw [pl,ql,eq])
  have multiplied : (L.1-K.1)*(P.1-Q.1) = 0 := by
    linear_combination -pl + pk + ql - qk
  have slopes : L.1 = K.1 := sub_eq_zero.mp
    ((mul_eq_zero.mp multiplied).resolve_right (sub_ne_zero.mpr abscissa))
  exact Prod.ext slopes (by
    rw [slopes] at pl
    exact add_left_cancel (pl.symm.trans pk))

private theorem affineGraph_no_square {F : Type*} [Field F] {u v w z : AffineVertex F}
    (uw : u ≠ w) (vz : v ≠ z)
    (uv : (affineGraph F).Adj u v) (vw : (affineGraph F).Adj v w)
    (wz : (affineGraph F).Adj w z) (zu : (affineGraph F).Adj z u) : False := by
  cases u <;> cases v <;> cases w <;> cases z <;>
    simp only [affineGraph,affineAdj,ne_eq,Sum.inl.injEq,Sum.inr.injEq] at uw vz uv vw wz zu <;> try contradiction
  · exact vz (line_through_two_unique uw uv zu vw wz)
  · exact uw (line_through_two_unique vz uv vw zu wz)

private theorem affineGraph_girth (F : Type*) [Field F] : (4 : ℕ∞) < (affineGraph F).egirth := by
  apply (by decide : (4 : ℕ∞) < 5).trans_le
  apply SimpleGraph.le_egirth.mpr
  intro a walk cycle
  by_contra! short
  have tooShort : walk.length < 5 := ENat.natCast_lt_natCast.mp short
  have atLeast := cycle.three_le_length
  have cases : walk.length = 3 ∨ walk.length = 4 := by omega
  rcases cases with three | four
  · obtain ⟨copy⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 3)).mpr ⟨a,walk,cycle,three⟩
    exact affineGraph_no_triangle
      (copy.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 3).Adj 0 1))
      (copy.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 3).Adj 1 2))
      (copy.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 3).Adj 2 0))
  · obtain ⟨copy⟩ := (SimpleGraph.cycleGraph_isContained_iff (by decide : 2 < 4)).mpr ⟨a,walk,cycle,four⟩
    exact affineGraph_no_square
      (copy.injective.ne (by decide : (0 : Fin 4) ≠ 2))
      (copy.injective.ne (by decide : (1 : Fin 4) ≠ 3))
      (copy.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 0 1))
      (copy.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 1 2))
      (copy.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 2 3))
      (copy.toHom.map_adj (by decide : (SimpleGraph.cycleGraph 4).Adj 3 0))

private theorem affineGraph_edgeCount (F : Type*) [Field F] [Fintype F] :
    (Fintype.card F)^3 ≤ Nat.card (affineGraph F).edgeSet := by
  let edge (t : F × F × F) : (affineGraph F).edgeSet :=
    ⟨s(Sum.inl (t.1,t.2.1*t.1+t.2.2),Sum.inr (t.2.1,t.2.2)),(affineGraph F).mem_edgeSet.mpr rfl⟩
  have inject : Function.Injective edge := by
    intro a b same
    have endpoints := Sym2.eq_iff.mp (congrArg Subtype.val same)
    rcases endpoints with ⟨first,second⟩ | ⟨clash,_⟩
    · have x := congrArg Prod.fst (Sum.inl.inj first)
      have line := Sum.inr.inj second
      exact Prod.ext x line
    · cases clash
  classical
  have bound := Nat.card_le_card_of_injective edge inject
  rw [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_prod] at bound
  simpa only [pow_succ,pow_zero,Nat.one_mul,Nat.mul_assoc] using bound

private theorem affineGraph_many_edges (C : ℕ) :
    ∃ n, ∃ G : SimpleGraph (Fin n), (4 : ℕ∞) < G.egirth ∧ C*n < Nat.card G.edgeSet := by
  classical
  obtain ⟨q,large,prime⟩ := Nat.exists_infinite_primes (2*C+1)
  let primeField : Fact q.Prime := ⟨prime⟩
  let F := ZMod q
  let V := AffineVertex F
  let n := Fintype.card V
  let number := Fintype.equivFin V
  let raw := affineGraph F
  let G := raw.comap number.symm
  let iso : G ≃g raw := SimpleGraph.Iso.comap number.symm raw
  have more : raw.egirth ≤ G.egirth := SimpleGraph.IsContained.egirth_le ⟨iso.toCopy⟩
  have sizes : Nat.card G.edgeSet = Nat.card raw.edgeSet := Nat.card_congr iso.mapEdgeSet
  have vertexCount : n = 2*q^2 := by
    simp only [n,V,Fintype.card_sum,Fintype.card_prod,F,ZMod.card]
    ring
  have edges : q^3 ≤ Nat.card raw.edgeSet := by
    simpa only [F,ZMod.card] using affineGraph_edgeCount F
  have gap : C*n < q^3 := by
    rw [vertexCount]
    calc
      C*(2*q^2) = (2*C)*q^2 := by ring
      _ < q*q^2 := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos prime.pos _)
      _ = q^3 := by ring
  exact ⟨n,G,(affineGraph_girth F).trans_le more,by rw [sizes]; exact gap.trans_le edges⟩

/-- Half-bridge exclusion through size four allows more than any fixed
multiple of the vertex count in opposite links. -/
theorem halfFour_no_linear_opposite_link_bound (C : ℕ) :
    ∃ n p : ℕ, ∃ paths : Fin p → List (Fin n),
      ∃ free : HalfBridgeFree (SourceAudit.BeforeIn paths) 4,
        (∀ i, (paths i).Nodup ∧ (paths i).length = 2) ∧
        C*n < Nat.card (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).edgeSet := by
  classical
  obtain ⟨n,G,girth,edges⟩ := affineGraph_many_edges C
  let p := Fintype.card G.Dart
  let index := Fintype.equivFin G.Dart
  let order : LinearOrder G.Dart := LinearOrder.lift' index index.injective
  let paths (i : Fin p) := dartPaths G (index.symm i)
  have full : BridgeFree (SourceAudit.BeforeIn (dartPaths G)) 4 := dartPaths_bridgeFree_of_lt_egirth G girth
  have outputFull : BridgeFree (SourceAudit.BeforeIn paths) 4 := by
    intro k limit
    exact ⟨fun bridge => (full limit).false
      (bridge.mapPaths index.symm index.symm.injective (fun _ _ _ step => step))⟩
  let out := oppositeLinkGraphOfHalfTwo paths (fun _ h => outputFull.halfFree (h.trans (by decide)))
  let prior := oppositeLinkGraphOfHalfTwo (dartPaths G) (fun _ h => full.halfFree (h.trans (by decide)))
  have related : out = prior := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · rintro ⟨a,b,ne,rest⟩
      exact ⟨index.symm a,index.symm b,index.symm.injective.ne ne,rest⟩
    · rintro ⟨a,b,ne,rest⟩
      refine ⟨index a,index b,index.injective.ne ne,?_⟩
      simpa only [paths,SourceAudit.BeforeIn,Equiv.symm_apply_apply] using rest
  have same : out = G := related.trans (dartPaths_oppositeLinkGraph G _)
  refine ⟨n,p,paths,outputFull.halfFree,fun i => ⟨dartPaths_nodup G (index.symm i),rfl⟩,?_⟩
  change C*n < Nat.card out.edgeSet
  rw [same]
  exact edges

end OnlineReachabilityPreservers
