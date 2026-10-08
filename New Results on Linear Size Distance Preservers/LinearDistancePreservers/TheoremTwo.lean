import LinearDistancePreservers.TreeCounting
import LinearDistancePreservers.MatchingExtremal

/-! Theorem 2, with a concrete constant and no supplied tree or path system.
`matchingNumber V` is the maximum edge count of an `|V|`-vertex graph whose
edges partition into `|V|` induced matchings, i.e. `n² / RS(n)` in the
paper's intended extremal normalization. -/
namespace LinearDistancePreservers
open Finset SimpleGraph LazyTreeSelection
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem theorem_two (G : SimpleGraph V) (P : Finset (V × V)) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ e ∈ P, H.edist e.1 e.2 = G.edist e.1 e.2) ∧
      H.edgeFinset.card ≤ 2 * P.card + 12 * matchingNumber V := by
  classical
  let D (s : V) : Finset V := univ.filter fun v => (s,v) ∈ P
  choose f hf hleaf hpres T hT using fun s => exists_lazy_tree G s (D s)
  let E : Finset (V × V) := univ.filter fun e => ∃ s, f s e.2 = some e.1
  let B : Finset (V × V) := univ.biUnion fun s => branchEdges (f s)
  let A := E \ B
  have hE : ∀ e ∈ E, G.Adj e.1 e.2 := by
    intro e he
    obtain ⟨s, hs⟩ := (mem_filter.mp he).2
    exact (hf s).2.1 e.2 e.1 hs |>.1
  have hD : ∑ s, (D s).card = P.card := by
    simp only [D, card_eq_sum_ones, sum_filter]
    rw [← Fintype.sum_prod_type (fun e : V × V => if e ∈ P then (1 : ℕ) else 0)]
    simp only [← sum_filter, ← card_eq_sum_ones, filter_mem_eq_inter, univ_inter]
  have hB : B.card ≤ 2 * P.card := by
    calc
      B.card ≤ ∑ s, (branchEdges (f s)).card := card_biUnion_le
      _ ≤ ∑ s, 2 * (D s).card := sum_le_sum (fun s _ =>
        branchEdges_le_two_demands (f s) (D s) (hleaf s))
      _ = _ := by rw [← mul_sum, hD]
  have hgood (e : V × V) (he : e ∈ A) : ∃ s, (T s).edge e.1 e.2 := by
    obtain ⟨heE, heB⟩ := mem_sdiff.mp he
    obtain ⟨s, hs⟩ := (mem_filter.mp heE).2
    refine ⟨s, (hT s e.1 e.2).mpr ⟨hs, ?_⟩⟩
    by_contra hsingle
    apply heB
    exact mem_biUnion.mpr ⟨s, mem_univ _, mem_filter.mpr ⟨mem_univ _, hs, hsingle⟩⟩
  let owner (e : V × V) := if h : e ∈ A then (hgood e h).choose else e.1
  have howner (e : V × V) (he : e ∈ A) : (T (owner e)).edge e.1 e.2 := by
    dsimp only [owner]
    rw [dif_pos he]
    exact (hgood e he).choose_spec
  obtain ⟨c, hc⟩ := exists_favorable_cut A (fun e he =>
    (hE e (mem_sdiff.mp he).1).ne)
  have hcut : (surviving A c).card ≤ 3 * matchingNumber V :=
    lazy_partition_bound (fun _ _ h => h.symm) (fun s => G.dist s) T
      (surviving A c) c owner (by
        intro e he
        obtain ⟨he, hcolor⟩ := mem_filter.mp he
        exact ⟨howner e he, hcolor⟩)
  have hA : A.card ≤ 12 * matchingNumber V := by omega
  have hsize : E.card ≤ 2 * P.card + 12 * matchingNumber V := by
    have hle : E.card ≤ A.card + B.card := card_le_card_sdiff_add_card
    omega
  let H : SimpleGraph V := {
    Adj := Span E
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun v h => (hE (v,v) (h.elim id id)).ne rfl⟩ }
  have hHG : H ≤ G := by
    intro u v h
    exact h.elim (fun he => hE (u,v) he) (fun he => (hE (v,u) he).symm)
  refine ⟨H, hHG, ?_, ?_⟩
  · intro e he
    have htH : treeGraph (hf e.1) ≤ H := by
      intro u v h
      exact h.elim
        (fun h => Or.inl (mem_filter.mpr ⟨mem_univ _, e.1, h⟩))
        (fun h => Or.inr (mem_filter.mpr ⟨mem_univ _, e.1, h⟩))
    apply le_antisymm _ (edist_anti hHG)
    exact (edist_anti htH).trans_eq (hpres e.1 e.2 (by simp [D, he]))
  · have hEdges : H.edgeFinset = E.image (fun e => s(e.1,e.2)) := by
      ext e
      induction e using Sym2.inductionOn with
      | hf u v =>
        simp only [mem_edgeFinset, H, Span, mem_image, Sym2.eq_iff]
        constructor
        · rintro (h | h)
          · exact ⟨(u,v), h, Or.inl ⟨rfl,rfl⟩⟩
          · exact ⟨(v,u), h, Or.inr ⟨rfl,rfl⟩⟩
        · rintro ⟨⟨a,b⟩, h, heq⟩
          rcases heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact Or.inl h
          · exact Or.inr h
    rw [hEdges]
    exact card_image_le.trans hsize

end LinearDistancePreservers
