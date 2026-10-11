import MinorFreeSpanners.CoreResidualBoundary

/-! Constructed initial connected partition. Every branch contains a selected
k-vertex connected core and only whole small residual components. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem exists_initial_connected_partition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (k : ℕ) (hk : 0<k)
    (hkN : k ≤ Fintype.card V) :
    ∃ P : Finset (Finset V), ∃ B : {S // S∈P} → Finset V,
      (∀ S : {S // S∈P}, S.val.card=k ∧ S.val ⊆ B S) ∧
      (∀ S T : {S // S∈P}, S≠T → Disjoint (B S) (B T)) ∧
      (∀ v : V, ∃ S : {S // S∈P}, v∈B S) ∧
      (∀ S : {S // S∈P}, ∀ x∈B S, ∀ y∈B S,
        ∃ p : G.Walk x y, (∀ z∈p.support, z∈B S) ∧ p.length ≤ 4*k) := by
  classical
  obtain ⟨P,hcore,hdis,hmax⟩ := exists_connected_core_packing G k hk
  let U := P.biUnion id
  let R := Uᶜ
  let Q := G.induce (R:Set V)
  let J := Q.ConnectedComponent
  let : Fintype J := Fintype.ofFinite J
  let W (c : J) := ResidualComponents.block G R c
  have hattach (c : J) : ∃ S∈P, ∃ x∈W c, ∃ y∈S, G.Adj x y :=
    (core_residual_boundary G hG k hkN P hmax c).2
  let owner (c : J) : {S // S∈P} :=
    ⟨(hattach c).choose,(hattach c).choose_spec.1⟩
  have hbridge (c : J) : ∃ x∈W c, ∃ y∈(owner c).val, G.Adj x y :=
    (hattach c).choose_spec.2
  let attached (S : {S // S∈P}) := (Finset.univ.filter fun c : J => owner c=S).biUnion W
  let B (S : {S // S∈P}) := S.val ∪ attached S
  have hmem (S : {S // S∈P}) (v : V) :
      v∈B S ↔ v∈S.val ∨ ∃ c : J, owner c=S ∧ v∈W c := by
    simp [B,attached]
  have hWU (c : J) : Disjoint (W c) U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    exact (Finset.mem_compl.mp (ResidualComponents.subset G R c hv)) hu
  have hSU (S : {S // S∈P}) : S.val ⊆ U := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨S.val,S.property,hv⟩
  have hWB (S : {S // S∈P}) (c : J) (he : owner c=S) : W c ⊆ B S := by
    intro v hv
    exact (hmem S v).mpr (Or.inr ⟨c,he,hv⟩)
  have hSB (S : {S // S∈P}) : S.val ⊆ B S := by
    intro v hv
    exact (hmem S v).mpr (Or.inl hv)
  have short (S : {S // S∈P}) (a : V) (ha : a∈S.val) (v : V) (hv : v∈B S) :
      ∃ p : G.Walk v a, (∀ z∈p.support, z∈B S) ∧ p.length < 2*k := by
    rcases (hmem S v).mp hv with hv | ⟨c,he,hv⟩
    · obtain ⟨p,hp,hl⟩ := (hcore S.val S.property).2.short_walk hv ha
      exact ⟨p,fun z hz => hSB S (hp z hz),by have hh:=(hcore S.val S.property).1;omega⟩
    · obtain ⟨x,hx,y,hy,hxy⟩ := hbridge c
      rw [he] at hy
      obtain ⟨p,hp,hlp⟩ := (ResidualComponents.connected G R c).short_walk hv hx
      obtain ⟨q,hq,hlq⟩ := (hcore S.val S.property).2.short_walk hy ha
      have hcsize := (core_residual_boundary G hG k hkN P hmax c).1
      refine ⟨p.append (.cons hxy q),?_,?_⟩
      · intro z hz
        rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
        · exact hWB S c he (hp z hz)
        · simp only [Walk.support_cons,List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hWB S c he hx
          · exact hSB S (hq z hz)
      · simp only [Walk.length_append,Walk.length_cons]
        have hh := (hcore S.val S.property).1
        change (W c).card < k at hcsize
        change p.length < (W c).card at hlp
        omega
  refine ⟨P,B,?_,?_,?_,?_⟩
  · intro S
    exact ⟨(hcore S.val S.property).1,hSB S⟩
  · intro S T hne
    apply Finset.disjoint_left.mpr
    intro v hvs hvt
    rcases (hmem S v).mp hvs with hs | ⟨c,hc,hvc⟩
    · rcases (hmem T v).mp hvt with ht | ⟨d,hd,hvd⟩
      · exact Finset.disjoint_left.mp (hdis S.val S.property T.val T.property
          (fun he => hne (Subtype.ext he))) hs ht
      · exact Finset.disjoint_left.mp (hWU d) hvd (hSU S hs)
    · rcases (hmem T v).mp hvt with ht | ⟨d,hd,hvd⟩
      · exact Finset.disjoint_left.mp (hWU c) hvc (hSU T ht)
      · by_cases he : c=d
        · subst d
          exact hne (hc.symm.trans hd)
        · exact Finset.disjoint_left.mp (ResidualComponents.disjoint G R c d he) hvc hvd
  · intro v
    by_cases hv : v∈U
    · obtain ⟨S,hS,hv⟩ := Finset.mem_biUnion.mp hv
      exact ⟨⟨S,hS⟩,hSB ⟨S,hS⟩ hv⟩
    · obtain ⟨c,hc⟩ := ResidualComponents.covers G R (Finset.mem_compl.mpr hv)
      exact ⟨owner c,hWB (owner c) c rfl hc⟩
  · intro S x hx y hy
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<S.val.card by rw [(hcore S.val S.property).1];exact hk)
    obtain ⟨p,hp,hlp⟩ := short S a ha x hx
    obtain ⟨q,hq,hlq⟩ := short S a ha y hy
    refine ⟨p.append q.reverse,?_,?_⟩
    · intro z hz
      rcases (Walk.mem_support_append_iff _ _).mp hz with hz | hz
      · exact hp z hz
      · exact hq z (by simpa using hz)
    · simp only [Walk.length_append,Walk.length_reverse]
      omega

end MinorFreeSpanners
