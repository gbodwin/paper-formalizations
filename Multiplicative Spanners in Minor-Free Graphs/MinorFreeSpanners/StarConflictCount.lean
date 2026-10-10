import MinorFreeSpanners.StarCenterReachability

/-! Actual conflict-count injections and the boundary of the reachable
star family. Each blocked center is charged to one distinct old leaf. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Distinct centers with a conflicting old leaf inject into actual A-neighbors. -/
theorem star_conflict_count {G : SimpleGraph V} {A B S : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) (w : V)
    (hconflict : ∀ b ∈ S, ∃ z ∈ L b, G.Adj w z) :
    S.card ≤ (A.filter fun z => G.Adj w z).card := by
  classical
  let T := A.filter fun z => G.Adj w z
  choose f hf hadj using fun b : S => hconflict b.val b.property
  let F : S → T := fun b => ⟨f b,Finset.mem_filter.mpr ⟨h.2.1 b.val (hf b),hadj b⟩⟩
  have hi : Function.Injective F := by
    intro b c he
    apply Subtype.ext
    by_contra hbc
    have hfc : f b = f c := congrArg (fun z : T => z.val) he
    exact Finset.disjoint_left.mp (h.2.2.2.2.1 b.val c.val hbc)
      (hf b) (hfc.symm ▸ hf c)
  have hc := Fintype.card_le_of_injective F hi
  simpa [T] using hc

omit [Fintype V] [DecidableEq V] in
/-- More B-neighbors than A-neighbors gives an actual compatible seed. -/
theorem exists_star_compatible_center {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) (w : V)
    (hdeg : (A.filter fun z => G.Adj w z).card <
      (B.filter fun b => G.Adj w b).card) :
    ∃ b ∈ B, StarCompatible G L w b := by
  classical
  by_contra hn
  have hc : ∀ b ∈ B.filter (fun b => G.Adj w b), ∃ z ∈ L b, G.Adj w z := by
    intro b hb
    obtain ⟨hbB,hbw⟩ := Finset.mem_filter.mp hb
    by_contra hz
    have hcompat : ∀ z ∈ L b, ¬ G.Adj w z := by
      intro z hzL he; exact hz ⟨z,hzL,he⟩
    exact hn ⟨b,hbB,hbw.symm,hcompat⟩
  exact (not_lt_of_ge (star_conflict_count h w hc)) hdeg

omit [DecidableEq V] in
/-- The reachable finite center set is actually nonempty when degree permits
an initial compatible edge. -/
theorem reachableStarCenters_nonempty {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) (w : V)
    (hdeg : (A.filter fun z => G.Adj w z).card <
      (B.filter fun b => G.Adj w b).card) :
    (reachableStarCenters G B L w).Nonempty := by
  classical
  obtain ⟨b,hb,hwb⟩ := exists_star_compatible_center h w hdeg
  exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hb,hwb,.refl⟩⟩

/-- Every neighbor outside the actual reachable family is blocked by a
conflicting old leaf, so its boundary degree is bounded by its A-degree. -/
theorem reachableStarCenters_boundary {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) (x : V)
    {w : V} (hw : w ∈ (reachableStarCenters G B L x).biUnion L) :
    ((B \ reachableStarCenters G B L x).filter fun b => G.Adj w b).card ≤
      (A.filter fun z => G.Adj w z).card := by
  classical
  obtain ⟨c,hc,hwc⟩ := Finset.mem_biUnion.mp hw
  apply star_conflict_count h w
  intro b hb
  obtain ⟨hbS,hbw⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbB,hbout⟩ := Finset.mem_sdiff.mp hbS
  by_contra hz
  have hcompat : StarCompatible G L w b := ⟨hbw.symm,fun z hzL he => hz ⟨z,hzL,he⟩⟩
  obtain ⟨s,hs,hxs,hr⟩ := (Finset.mem_filter.mp hc).2
  have hcB := reachableStarCenters_subset G B L x hc
  have harc : StarCenterStep G B L c b := ⟨hcB,hbB,w,hwc,hcompat⟩
  exact hbout (Finset.mem_filter.mpr ⟨Finset.mem_univ _,s,hs,hxs,hr.tail harc⟩)

end MinorFreeSpanners
