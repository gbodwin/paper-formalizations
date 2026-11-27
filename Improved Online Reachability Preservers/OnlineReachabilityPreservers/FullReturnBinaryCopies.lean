import OnlineReachabilityPreservers.FullReturnCopyColours

/-! Bound the new support when only a few of the original copies may split. -/

namespace OnlineReachabilityPreservers

open Finset

/-- With two colours, each permitted exception consumes at most one
additional vertex label. Every other vertex uses its fixed base colour. -/
theorem colourListRows_activeVertices_le_binary {V I : Type*} [LinearOrder V] [Fintype V]
    [Fintype I] (rows : I → List V) (exceptions : Finset V)
    (base : V → Fin 2) (colour : I → V → Fin 2)
    (fixed : ∀ i v, v ∈ rows i → v ∉ exceptions → colour i v = base v) :
    (activeListVertices (colourListRows rows colour)).card ≤ Fintype.card V + exceptions.card := by
  let first := univ.image (fun v : V => toLex (v,base v))
  let second := exceptions.image (fun v => toLex (v,(base v).rev))
  have supports : activeListVertices (colourListRows rows colour) ⊆ first ∪ second := by
    intro w present
    obtain ⟨i,_,use⟩ := mem_biUnion.mp present
    obtain ⟨on,tag⟩ := mem_colourListRows.mp (List.mem_toFinset.mp use)
    let v := (ofLex w).1
    apply mem_union.mpr
    by_cases standard : colour i v = base v
    · exact Or.inl (mem_image.mpr ⟨v,mem_univ _,ofLex.injective (Prod.ext rfl (tag.trans standard).symm)⟩)
    · have marked : v ∈ exceptions := by
        by_contra absent
        exact standard (fixed i v on absent)
      have other : colour i v = (base v).rev := by
        apply Fin.ext
        rw [Fin.val_rev]
        have diff : (colour i v).val ≠ (base v).val := fun equal => standard (Fin.ext equal)
        have left := (colour i v).isLt
        have right := (base v).isLt
        omega
      exact Or.inr (mem_image.mpr ⟨v,marked,ofLex.injective (Prod.ext rfl (tag.trans other).symm)⟩)
  exact (card_le_card supports).trans ((card_union_le first second).trans
    (Nat.add_le_add (card_image_le.trans_eq card_univ) card_image_le))

/-- With mean degree at least eight, the original degree copies have
room for a binary refinement at up to seven ninety-thirds of the
original vertex count. A separating refinement on that many copies
therefore satisfies the support bound for full cleaning. -/
theorem hasCrossedReturnWidthColours_of_small_binary_repair {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : 8*n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (repair : let M := ∑ i, (paths i).length
      let D := 4*M/n
      let L := 4*M/p
      let W := ListVertexBlockIndex paths D
      let copies := splitListVertices paths D
      ∃ (exceptions : Finset W) (base : W → Fin 2) (colour : Fin p → W → Fin 2),
        93*exceptions.card ≤ 7*n ∧
          (∀ i w, w ∈ copies i → w ∉ exceptions → colour i w = base w) ∧
          NoColourCompatibleCrossedReturn copies (splitListPaths copies L) Sigma.fst colour (cutoff-5)) :
    HasCrossedReturnWidthColours paths cutoff := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let W := ListVertexBlockIndex paths D
  let copies := splitListVertices paths D
  let J := ListBlockIndex copies L
  let pieces : J → List W := splitListPaths copies L
  obtain ⟨exceptions,base,colour,budget,fixed,safe⟩ := repair
  refine ⟨2,colour,safe,?_⟩
  obtain ⟨dPos,_,_⟩ := four_average_width hn (show n ≤ M by omega)
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  have raw := (regularization_list_counts paths simple dPos lPos).1
  simp only [Fintype.card_fin] at raw
  change Fintype.card W ≤ n+M/D at raw
  have cap : 31*(M/D) ≤ 8*n := large_average_width_budget hn dense
  have original : 31*Fintype.card W ≤ 39*n := by omega
  have used := colourListRows_activeVertices_le_binary pieces exceptions base (colour ∘ Sigma.fst)
    (fun i w on absent => fixed i.fst w (mem_localPathBlock.mp on).1 absent)
  change 3*(activeListVertices (colourListRows pieces (colour ∘ Sigma.fst))).card ≤ 4*n
  omega

end OnlineReachabilityPreservers
