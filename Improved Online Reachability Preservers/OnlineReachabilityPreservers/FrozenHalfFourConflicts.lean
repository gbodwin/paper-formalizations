import OnlineReachabilityPreservers.ContiguousHalfCleaning
import OnlineReachabilityPreservers.ReverseIntersectionCopies

/-! Repair nested half-four conflicts and count the surviving path incidences. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

section Repair

variable {p : ℕ} {J V : Type*} [DecidableEq V]

/-- A nested reversal needs these two incidences at its late central
corner, one on the central piece and one on the later inner piece. -/
def NestedCutConflict (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) (a b : J × V) : Prop :=
  a.2 = b.2 ∧
    ∃ (early outer : J) (u v z : V),
      early ≠ a.1 ∧ parent early = parent a.1 ∧
      parent outer ≠ parent early ∧ parent outer ≠ parent b.1 ∧ parent early < parent b.1 ∧
      Before paths (parent early) v a.2 ∧
      Before pieces early u v ∧ Before pieces a.1 a.2 z ∧
      Before pieces outer z u ∧ Before pieces b.1 b.2 v

theorem NestedCutConflict.left_mem {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b : J × V} (edge : NestedCutConflict paths pieces parent a b) :
    a.2 ∈ pieces a.1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,late,_,_⟩ := edge
  exact late.1

theorem NestedCutConflict.right_mem {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b : J × V} (edge : NestedCutConflict paths pieces parent a b) :
    b.2 ∈ pieces b.1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,inner⟩ := edge
  exact inner.1

theorem NestedCutConflict.reversePartner {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b : J × V} (edge : NestedCutConflict paths pieces parent a b)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y) :
    LaterReversePartner paths a.2 (parent a.1) (parent b.1) := by
  obtain ⟨same,_,_,_,v,_,_,parents,_,_,arrival,mid,_,_,_,inner⟩ := edge
  exact ⟨parents ▸ arrival,v,parents ▸ mid,same.symm ▸ steps inner⟩

theorem NestedCutConflict.out_unique {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} {a b c : J × V}
    (free : HalfBridgeFree (Before paths) 4)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ab : NestedCutConflict paths pieces parent a b) (ac : NestedCutConflict paths pieces parent a c) :
    b = c := by
  have labels := laterReversePartner_unique free (by decide)
    (ab.reversePartner (fun {_ _ _} => steps)) (ac.reversePartner (fun {_ _ _} => steps))
  have vertex : b.2 = c.2 := ab.1.symm.trans ac.1
  have piece : b.1 = c.1 := by
    by_contra different
    exact apart different labels ab.right_mem (vertex.symm ▸ ac.right_mem)
  exact Prod.ext piece vertex

variable [Fintype J] [Fintype V]

noncomputable def nestedCutSources (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) : Finset (J × V) := by
  classical
  exact univ.filter fun a => ∃ b, NestedCutConflict paths pieces parent a b

noncomputable def nestedCutTargets (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) : Finset (J × V) := by
  classical
  exact univ.filter fun b => ∃ a, NestedCutConflict paths pieces parent a b

theorem nestedCutTargets_card_le_sources {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p}
    (free : HalfBridgeFree (Before paths) 4)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False) :
    (nestedCutTargets paths pieces parent).card ≤ (nestedCutSources paths pieces parent).card := by
  classical
  let S := nestedCutSources paths pieces parent
  let T := nestedCutTargets paths pieces parent
  have out (a : S) : ∃ b, NestedCutConflict paths pieces parent a.val b :=
    (mem_filter.mp a.property).2
  let map (a : S) : T := ⟨(out a).choose,mem_filter.mpr ⟨mem_univ _,a.val,(out a).choose_spec⟩⟩
  have onto : Function.Surjective map := by
    intro b
    obtain ⟨a,edge⟩ := (mem_filter.mp b.property).2
    let row : S := ⟨a,mem_filter.mpr ⟨mem_univ _,b.val,edge⟩⟩
    refine ⟨row,Subtype.ext ?_⟩
    exact NestedCutConflict.out_unique free (fun {_ _ _} => steps) (fun {_ _ _} => apart)
      (out row).choose_spec edge
  simpa only [Fintype.card_coe] using Fintype.card_le_of_surjective map onto

noncomputable def nestedCutDeletion (paths : Fin p → List V) (pieces : J → List V)
    (parent : J → Fin p) (c : Bool) : Finset (J × V) := by
  classical
  exact (nestedCutSources paths pieces parent ∪ nestedCutTargets paths pieces parent).filter
    fun a => reversePartnerColor paths a.2 (parent a.1) = c

theorem nestedCutDeletion_covers {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} (free : HalfBridgeFree (Before paths) 4)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (c : Bool) {a b : J × V} (edge : NestedCutConflict paths pieces parent a b) :
    a ∈ nestedCutDeletion paths pieces parent c ∨ b ∈ nestedCutDeletion paths pieces parent c := by
  classical
  have aIn : a ∈ nestedCutSources paths pieces parent := mem_filter.mpr ⟨mem_univ _,b,edge⟩
  have bIn : b ∈ nestedCutTargets paths pieces parent := mem_filter.mpr ⟨mem_univ _,a,edge⟩
  have sep := reversePartnerColor_ne free (by decide) (edge.reversePartner (fun {_ _ _} => steps))
  let colA := reversePartnerColor paths a.2 (parent a.1)
  let colB := reversePartnerColor paths b.2 (parent b.1)
  have different : colA ≠ colB := by simpa only [colA,colB,← edge.1] using sep
  have chooseColor (a b c : Bool) (different : a ≠ b) : a = c ∨ b = c := by
    cases a <;> cases b <;> cases c <;> simp_all
  have chosen := chooseColor colA colB c different
  rcases chosen with selectA | selectB
  · exact Or.inl (mem_filter.mpr ⟨mem_union_left _ aIn,selectA⟩)
  · exact Or.inr (mem_filter.mpr ⟨mem_union_right _ bIn,selectB⟩)

private theorem nestedCutDeletion_union [DecidableEq J] (paths : Fin p → List V) (pieces : J → List V) (parent : J → Fin p) :
    nestedCutDeletion paths pieces parent false ∪ nestedCutDeletion paths pieces parent true =
      nestedCutSources paths pieces parent ∪ nestedCutTargets paths pieces parent := by
  classical
  ext a
  cases h : reversePartnerColor paths a.2 (parent a.1) <;> simp [nestedCutDeletion,h]

private theorem nestedCutDeletion_disjoint (paths : Fin p → List V) (pieces : J → List V) (parent : J → Fin p) :
    Disjoint (nestedCutDeletion paths pieces parent false) (nestedCutDeletion paths pieces parent true) := by
  classical
  rw [disjoint_left]
  intro a left right
  exact Bool.false_ne_true ((mem_filter.mp left).2.symm.trans (mem_filter.mp right).2)

/-- If all sources of cut conflicts are on heavy pieces, every target on
a heavy piece saves one slot in the bound on the involved light incidences. -/
theorem nestedCut_light_card_add_heavy_targets_le [DecidableEq J] {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} (free : HalfBridgeFree (Before paths) 4)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (heavy : Finset (J × V)) (inHeavy : nestedCutSources paths pieces parent ⊆ heavy) :
    ((nestedCutSources paths pieces parent ∪ nestedCutTargets paths pieces parent) \ heavy).card +
      (nestedCutTargets paths pieces parent ∩ heavy).card ≤ (nestedCutSources paths pieces parent).card := by
  classical
  let S := nestedCutSources paths pieces parent
  let T := nestedCutTargets paths pieces parent
  have light : (S ∪ T) \ heavy = T \ (T ∩ heavy) := by
    ext a
    simp only [mem_sdiff,mem_union,mem_inter]
    constructor
    · rintro ⟨source | target,out⟩
      · exact (out (inHeavy source)).elim
      · exact ⟨target,fun pair => out pair.2⟩
    · exact fun ⟨target,out⟩ => ⟨Or.inr target,fun mem => out ⟨target,mem⟩⟩
  rw [show (nestedCutSources paths pieces parent ∪ nestedCutTargets paths pieces parent) \ heavy =
    T \ (T ∩ heavy) from light,card_sdiff_add_card_eq_card inter_subset_left]
  exact nestedCutTargets_card_le_sources free (fun {_ _ _} => steps) (fun {_ _ _} => disjoint)

noncomputable def erasePieceIncidences (pieces : J → List V) (deleted : Finset (J × V))
    (i : J) : List V := by
  classical
  exact (pieces i).filter fun v => decide ((i,v) ∉ deleted)

omit [Fintype J] [Fintype V] in
theorem erasePieceIncidences_sublist (pieces : J → List V) (deleted : Finset (J × V)) (i : J) :
    (erasePieceIncidences pieces deleted i).Sublist (pieces i) := List.filter_sublist

omit [Fintype J] [Fintype V] in
theorem mem_erasePieceIncidences {pieces : J → List V} {deleted : Finset (J × V)} {i : J} {v : V} :
    v ∈ erasePieceIncidences pieces deleted i ↔ v ∈ pieces i ∧ (i,v) ∉ deleted := by
  simp [erasePieceIncidences]

omit [Fintype J] [Fintype V] in
/-- Removing a cover of the nested cut conflicts preserves half-four exclusion. -/
theorem erasePieceIncidences_halfFree [LinearOrder J] {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} (free : HalfBridgeFree (Before paths) 4)
    (simple : ∀ i, (pieces i).Nodup) (monotone : Monotone parent)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (disjoint : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (ordered : ∀ {i j}, i ≠ j → parent i = parent j →
      (∀ ⦃x y⦄, x ∈ pieces i → y ∈ pieces j → Before paths (parent i) x y) ∨
      (∀ ⦃x y⦄, x ∈ pieces j → y ∈ pieces i → Before paths (parent i) x y))
    (deleted : Finset (J × V))
    (cover : ∀ {a b}, NestedCutConflict paths pieces parent a b → a ∈ deleted ∨ b ∈ deleted) :
    HalfBridgeFree (Before (erasePieceIncidences pieces deleted)) 4 := by
  let clean := erasePieceIncidences pieces deleted
  have contained {i : J} {w : V} (on : w ∈ clean i) : w ∈ pieces i :=
    (mem_erasePieceIncidences.mp on).1
  have lift {i x y} (step : Before clean i x y) : Before pieces i x y :=
    listBefore_of_sublist (simple i) (erasePieceIncidences_sublist pieces deleted i) step
  apply (free.split_ordered_iff_no_retained_nested parent monotone
    (fun h => steps (lift h)) (fun ne eq left right => disjoint ne eq (contained left) (contained right)) ?_).mpr
  · rintro ⟨inner,w,early,late,outer,u,v,z,neq,same,outerEarly,outerInner,earlier,vw,uv,wz,zu,wv⟩
    have edge : NestedCutConflict paths pieces parent (late,w) (inner,w) :=
      ⟨rfl,early,outer,u,v,z,neq,same,outerEarly,outerInner,earlier,vw,lift uv,lift wz,lift zu,lift wv⟩
    exact (cover edge).elim (mem_erasePieceIncidences.mp wz.1).2 (mem_erasePieceIncidences.mp wv.1).2
  · intro i j different same
    rcases ordered different same with before | after
    · exact Or.inl (fun {_ _} left right => before (contained left) (contained right))
    · exact Or.inr (fun {_ _} left right => after (contained left) (contained right))

variable [DecidableEq J]

/-- The incidences carried by the designated rows, with each row occurrence counted once. -/
noncomputable def pieceIncidences (pieces : J → List V) (rows : Finset J) : Finset (J × V) :=
  (rows.product univ).filter fun a => a.2 ∈ pieces a.1

omit [Fintype J] [DecidableEq J] in
theorem mem_pieceIncidences {pieces : J → List V} {rows : Finset J} {a : J × V} :
    a ∈ pieceIncidences pieces rows ↔ a.1 ∈ rows ∧ a.2 ∈ pieces a.1 := by
  simp [pieceIncidences]

omit [Fintype J] [DecidableEq J] in
theorem pieceIncidences_card {pieces : J → List V} (simple : ∀ i, (pieces i).Nodup)
    (rows : Finset J) : (pieceIncidences pieces rows).card = ∑ i ∈ rows, (pieces i).length := by
  calc
    _ = ∑ a ∈ rows.product (univ : Finset V), (if a.2 ∈ pieces a.1 then 1 else 0) := by
      rw [pieceIncidences,card_filter]
    _ = ∑ i ∈ rows, ∑ v : V, (if v ∈ pieces i then 1 else 0) :=
      Finset.sum_product' _ _ (fun i v => if v ∈ pieces i then 1 else 0)
    _ = _ := by
      refine sum_congr rfl fun i _ => ?_
      rw [← card_filter]
      have extent : univ.filter (fun v => v ∈ pieces i) = (pieces i).toFinset := by ext v; simp
      rw [extent,List.toFinset_card_of_nodup (simple i)]

omit [Fintype J] in
private theorem pieceIncidences_erase (pieces : J → List V) (rows : Finset J) (deleted : Finset (J × V)) :
    pieceIncidences (erasePieceIncidences pieces deleted) rows = pieceIncidences pieces rows \ deleted := by
  ext a
  simp only [mem_pieceIncidences,mem_erasePieceIncidences,mem_sdiff,and_assoc]

omit [Fintype J] in
private theorem erased_mass_add_loss {pieces : J → List V} (simple : ∀ i, (pieces i).Nodup)
    (rows : Finset J) (deleted : Finset (J × V)) :
    (∑ i ∈ rows, (erasePieceIncidences pieces deleted i).length) +
      (pieceIncidences pieces rows ∩ deleted).card = ∑ i ∈ rows, (pieces i).length := by
  have cleanSimple (i : J) := (erasePieceIncidences_sublist pieces deleted i).nodup (simple i)
  rw [← pieceIncidences_card simple rows,← pieceIncidences_card cleanSimple rows,pieceIncidences_erase]
  exact card_sdiff_add_card_inter (pieceIncidences pieces rows) deleted

omit [Fintype J] in
private theorem erased_two_colors_mass {pieces : J → List V} (simple : ∀ i, (pieces i).Nodup)
    (rows : Finset J) {left right : Finset (J × V)} (disjoint : Disjoint left right) :
    (∑ i ∈ rows, (erasePieceIncidences pieces left i).length) +
      (∑ i ∈ rows, (erasePieceIncidences pieces right i).length) +
      (pieceIncidences pieces rows ∩ (left ∪ right)).card = 2*(∑ i ∈ rows, (pieces i).length) := by
  have leftMass := erased_mass_add_loss simple rows left
  have rightMass := erased_mass_add_loss simple rows right
  rw [inter_union_distrib_left,card_union_of_disjoint]
  · omega
  · exact disjoint.mono inter_subset_right inter_subset_right

/-- A cover of the nested conflicts either leaves three tenths of the total
mass on the heavy pieces alone or leaves at least 337/650 of the total mass
within the path budget. The light-piece allowance pays for the row trimming. -/
theorem nestedCut_repair_budget {paths : Fin p → List V} {pieces : J → List V}
    {parent : J → Fin p} (free : HalfBridgeFree (Before paths) 4)
    (simple : ∀ i, (pieces i).Nodup)
    (steps : ∀ {i x y}, Before pieces i x y → Before paths (parent i) x y)
    (apart : ∀ {i j x}, i ≠ j → parent i = parent j → x ∈ pieces i → x ∈ pieces j → False)
    (heavy light : Finset J) (separate : Disjoint heavy light)
    (coversRows : ∀ i, pieces i ≠ [] → i ∈ heavy ∪ light)
    (sourcesHeavy : nestedCutSources paths pieces parent ⊆ pieceIncidences pieces heavy)
    (heavyFits : heavy.card ≤ p) (lightRoom : 11*light.card ≤ 13*(p-heavy.card))
    (moderate : 50*(∑ i ∈ heavy, (pieces i).length) ≤ 29*(∑ i, (pieces i).length)) :
    ∃ (deleted : Finset (J × V)) (kept : Finset J),
      (∀ {a b}, NestedCutConflict paths pieces parent a b → a ∈ deleted ∨ b ∈ deleted) ∧
      kept.card ≤ p ∧
      ((kept = heavy ∧ 3*(∑ i, (pieces i).length) ≤ 10*(∑ i ∈ kept,
        (erasePieceIncidences pieces deleted i).length)) ∨
        337*(∑ i, (pieces i).length) ≤ 650*(∑ i ∈ kept, (erasePieceIncidences pieces deleted i).length)) := by
  classical
  let M := ∑ i, (pieces i).length
  let S := ∑ i ∈ heavy, (pieces i).length
  let U := ∑ i ∈ light, (pieces i).length
  let sources := nestedCutSources paths pieces parent
  let targets := nestedCutTargets paths pieces parent
  let heavyInc := pieceIncidences pieces heavy
  let B := (targets ∩ heavyInc).card
  have parts : S+U = M := by
    rw [show S+U = ∑ i ∈ heavy ∪ light, (pieces i).length from (sum_union separate).symm]
    apply sum_subset (subset_univ _)
    intro i _ out
    have empty : pieces i = [] := of_not_not (fun nonempty => out (coversRows i nonempty))
    rw [empty,List.length_nil]
  change 50*S ≤ 29*M at moderate
  by_cases enoughHeavy : 3*M+10*B ≤ 10*S
  · refine ⟨targets,heavy,?_,heavyFits,Or.inl ⟨rfl,?_⟩⟩
    · exact fun {a b} edge => Or.inr (mem_filter.mpr ⟨mem_univ _,a,edge⟩)
    · have mass := erased_mass_add_loss simple heavy targets
      rw [inter_comm] at mass
      change (∑ i ∈ heavy, (erasePieceIncidences pieces targets i).length)+B = S at mass
      change 3*M ≤ 10*(∑ i ∈ heavy, (erasePieceIncidences pieces targets i).length)
      omega
  let deleted (c : Bool) := nestedCutDeletion paths pieces parent c
  let weight (c : Bool) (i : J) := (erasePieceIncidences pieces (deleted c) i).length
  have split : deleted false ∪ deleted true = sources ∪ targets := nestedCutDeletion_union _ _ _
  have separateColors : Disjoint (deleted false) (deleted true) := nestedCutDeletion_disjoint _ _ _
  have retainHeavy :
      S ≤ (∑ i ∈ heavy, weight false i)+(∑ i ∈ heavy, weight true i) := by
    have eq := erased_two_colors_mass simple heavy separateColors
    have le : (heavyInc ∩ (deleted false ∪ deleted true)).card ≤ S := by
      exact (card_le_card inter_subset_left).trans_eq (pieceIncidences_card simple heavy)
    change (∑ i ∈ heavy, weight false i)+(∑ i ∈ heavy, weight true i)+
      (heavyInc ∩ (deleted false ∪ deleted true)).card = 2*S at eq
    omega
  have lightLoss : (pieceIncidences pieces light ∩ (sources ∪ targets)).card+B ≤ S := by
    have count : ((sources ∪ targets) \ heavyInc).card+B ≤ sources.card :=
      nestedCut_light_card_add_heavy_targets_le free (fun {_ _ _} => steps) (fun {_ _ _} => apart) _ sourcesHeavy
    have subset : pieceIncidences pieces light ∩ (sources ∪ targets) ⊆ (sources ∪ targets) \ heavyInc := by
      intro a member
      obtain ⟨onLight,incident⟩ := mem_inter.mp member
      exact mem_sdiff.mpr ⟨incident,fun onHeavy => disjoint_left.mp separate
        (mem_pieceIncidences.mp onHeavy).1 (mem_pieceIncidences.mp onLight).1⟩
    have sourceCount : sources.card ≤ S := (card_le_card sourcesHeavy).trans_eq (pieceIncidences_card simple _)
    have le := card_le_card subset
    omega
  have retainLight :
      2*U+B ≤ (∑ i ∈ light, weight false i)+(∑ i ∈ light, weight true i)+S := by
    have eq := erased_two_colors_mass simple light separateColors
    rw [split] at eq
    change (∑ i ∈ light, weight false i)+(∑ i ∈ light, weight true i)+
      (pieceIncidences pieces light ∩ (sources ∪ targets)).card = 2*U at eq
    omega
  have trimmed (c : Bool) : ∃ rows : Finset J, rows.card ≤ p ∧
      13*(∑ i ∈ heavy, weight c i)+11*(∑ i ∈ light, weight c i) ≤ 13*(∑ i ∈ rows, weight c i) := by
    obtain ⟨kept,inside,count,retained⟩ := trim_weights_ratio light (weight c)
      (show 11 ≤ 13 by decide) lightRoom
    have disjoint := separate.mono_right inside
    refine ⟨heavy ∪ kept,?_,?_⟩
    · rw [card_union_of_disjoint disjoint]
      omega
    · rw [sum_union disjoint,Nat.mul_add]
      omega
  obtain ⟨zero,zeroFits,zeroMass⟩ := trimmed false
  obtain ⟨one,oneFits,oneMass⟩ := trimmed true
  let K₀ := ∑ i ∈ zero, weight false i
  let K₁ := ∑ i ∈ one, weight true i
  have large : 337*M ≤ 325*(K₀+K₁) := by
    change _ ≤ 13*K₀ at zeroMass
    change _ ≤ 13*K₁ at oneMass
    omega
  obtain ⟨c,rows,cap,mass⟩ : ∃ (c : Bool) (rows : Finset J), rows.card ≤ p ∧
      337*M ≤ 650*(∑ i ∈ rows, weight c i) := by
    by_cases zeroEnough : 337*M ≤ 650*K₀
    · exact ⟨false,zero,zeroFits,zeroEnough⟩
    · exact ⟨true,one,oneFits,by change 337*M ≤ 650*K₁; omega⟩
  exact ⟨deleted c,rows,(fun {_ _} edge => nestedCutDeletion_covers free
    (fun {_ _ _} => steps) c edge),cap,Or.inr mass⟩

end Repair

end OnlineReachabilityPreservers
