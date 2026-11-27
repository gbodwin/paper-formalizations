import OnlineReachabilityPreservers.HalfFiveDegreeFirstCleaning

/-! Cover edges that increase a rank and have at most one target from each source. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The two endpoints of an ordered pair. -/
def cutEdgeEndpoints {A : Type*} [DecidableEq A] (e : A × A) : Finset A :=
  {e.1,e.2}

/-- A finite set of edges in the given support with disjoint endpoints. -/
def CutMatching {A : Type*} [DecidableEq A] (edge : A → A → Prop) (support : Finset A)
    (matching : Finset (A × A)) : Prop :=
  (∀ e ∈ matching, e.1 ∈ support ∧ e.2 ∈ support ∧ edge e.1 e.2) ∧
    ∀ e ∈ matching, ∀ f ∈ matching, e ≠ f → Disjoint (cutEdgeEndpoints e) (cutEdgeEndpoints f)

/-- If edges increase a rank and each source has at most one target, an
edge cover by vertices and a matching can be chosen with equal sizes. -/
theorem exists_cut_cover_and_matching {A : Type*} [DecidableEq A] (edge : A → A → Prop)
    (rank : A → ℕ) (increases : ∀ {a b}, edge a b → rank a < rank b)
    (oneTarget : ∀ {a b c}, edge a b → edge a c → b = c)
    (support : Finset A) :
    ∃ cover ⊆ support, ∃ matching : Finset (A × A),
      cover.card = matching.card ∧
      (∀ a ∈ support, ∀ b ∈ support, edge a b → a ∈ cover ∨ b ∈ cover) ∧
      CutMatching edge support matching := by
  classical
  induction support using Finset.strongInduction with
  | H support ih =>
    let sources := support.filter fun a => ∃ b ∈ support, edge a b
    by_cases active : sources.Nonempty
    · obtain ⟨x,inSources,least⟩ := exists_min_image sources rank active
      obtain ⟨xOn,y,yOn,xy⟩ := mem_filter.mp inSources
      have noIncoming {z : A} (inside : z ∈ support) (zx : edge z x) : False :=
        (increases zx).not_ge (least z (mem_filter.mpr ⟨inside,x,xOn,zx⟩))
      let rest := (support.erase x).erase y
      have inside : rest ⊆ support := (erase_subset _ _).trans (erase_subset _ _)
      have outsideX {z : A} (hz : z ∈ rest) : z ≠ x := (mem_erase.mp (mem_erase.mp hz).2).1
      have outsideY {z : A} (hz : z ∈ rest) : z ≠ y := (mem_erase.mp hz).1
      have smaller : rest ⊂ support := lt_of_le_of_ne inside (fun eq => outsideX (eq ▸ xOn) rfl)
      obtain ⟨cover,coverSub,matching,size,covered,matched,separate⟩ := ih rest smaller
      have freshV : y ∉ cover := fun hy => outsideY (coverSub hy) rfl
      have freshE : (x,y) ∉ matching := fun he => outsideX ((matched _ he).1) rfl
      have newDisjoint {e : A × A} (old : e ∈ matching) :
          Disjoint (cutEdgeEndpoints (x,y)) (cutEdgeEndpoints e) := by
        apply disjoint_left.mpr
        intro z onNew onOld
        have alternatives : z = x ∨ z = y := by simpa [cutEdgeEndpoints] using onNew
        have zOn : z ∈ rest := by
          have ends : z = e.1 ∨ z = e.2 := by simpa [cutEdgeEndpoints] using onOld
          exact ends.elim (fun eq => eq ▸ (matched e old).1) (fun eq => eq ▸ (matched e old).2.1)
        exact alternatives.elim (outsideX zOn) (outsideY zOn)
      have newSubset : insert y cover ⊆ support := by
        intro a ha
        rcases mem_insert.mp ha with rfl | old
        · exact yOn
        · exact inside (coverSub old)
      refine ⟨insert y cover,newSubset,
        insert (x,y) matching,?_,?_,?_,?_⟩
      · rw [card_insert_of_notMem freshV,card_insert_of_notMem freshE,size]
      · intro a aOn b bOn ab
        by_cases aY : a = y
        · exact Or.inl (mem_insert.mpr (Or.inl aY))
        by_cases bY : b = y
        · exact Or.inr (mem_insert.mpr (Or.inl bY))
        by_cases aX : a = x
        · subst a
          exact (bY (oneTarget ab xy)).elim
        by_cases bX : b = x
        · subst b
          exact (noIncoming aOn ab).elim
        have ra : a ∈ rest := mem_erase.mpr ⟨aY,mem_erase.mpr ⟨aX,aOn⟩⟩
        have rb : b ∈ rest := mem_erase.mpr ⟨bY,mem_erase.mpr ⟨bX,bOn⟩⟩
        exact (covered a ra b rb ab).imp
          (fun h => mem_insert.mpr (Or.inr h)) (fun h => mem_insert.mpr (Or.inr h))
      · intro e member
        rcases mem_insert.mp member with new | old
        · subst e
          exact ⟨xOn,yOn,xy⟩
        · obtain ⟨left,right,relation⟩ := matched e old
          exact ⟨inside left,inside right,relation⟩
      · intro e he f hf different
        rcases mem_insert.mp he with eNew | eOld
        · subst e
          rcases mem_insert.mp hf with fNew | fOld
          · exact (different fNew.symm).elim
          · exact newDisjoint fOld
        · rcases mem_insert.mp hf with fNew | fOld
          · subst f
            exact (newDisjoint eOld).symm
          · exact separate e eOld f fOld different
    · refine ⟨∅,empty_subset _,∅,rfl,?_,?_⟩
      · intro a aOn b bOn ab
        exact (active ⟨a,mem_filter.mpr ⟨aOn,b,bOn,ab⟩⟩).elim
      · simp [CutMatching]

/-- Every edge cover by vertices contains at least as many vertices
as any matching in the supported edges. -/
theorem CutMatching.card_le_cover {A : Type*} [DecidableEq A] {edge : A → A → Prop}
    {support : Finset A} {matching : Finset (A × A)} (matched : CutMatching edge support matching)
    (cover : Finset A) (covers : ∀ a ∈ support, ∀ b ∈ support, edge a b → a ∈ cover ∨ b ∈ cover) :
    matching.card ≤ cover.card := by
  classical
  have hits (e : matching) : ∃ a : cover, a.val ∈ cutEdgeEndpoints e.val := by
    obtain ⟨left,right,step⟩ := matched.1 e.val e.property
    rcases covers _ left _ right step with first | second
    · exact ⟨⟨e.val.1,first⟩,by simp [cutEdgeEndpoints]⟩
    · exact ⟨⟨e.val.2,second⟩,by simp [cutEdgeEndpoints]⟩
  let chosen (e : matching) := Classical.choose (hits e)
  have injective : Function.Injective chosen := by
    intro e f same
    apply Subtype.ext
    by_contra different
    have separate := matched.2 e.val e.property f.val f.property different
    have first : (chosen e).val ∈ cutEdgeEndpoints e.val := Classical.choose_spec (hits e)
    have second : (chosen f).val ∈ cutEdgeEndpoints f.val := Classical.choose_spec (hits f)
    exact disjoint_left.mp separate first (same.symm ▸ second)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective chosen injective

open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- The actual degree-first cut relation has a cover of the same size as
a matching of its edges. -/
theorem degreeFirstCut_cover_and_matching {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) (D L : ℕ) :
    let support := pieceIncidences (listRegularizedPaths paths D L) univ
    ∃ cover ⊆ support, ∃ matching,
      cover.card = matching.card ∧
      (∀ {a b}, DegreeFirstCutConflict paths D L a b → a ∈ cover ∨ b ∈ cover) ∧
      CutMatching (DegreeFirstCutConflict paths D L) support matching := by
  let J := ListBlockIndex (splitListVertices paths D) L
  let V := ListVertexBlockIndex paths D
  let support := pieceIncidences (listRegularizedPaths paths D L) univ
  let rank (a : J × V) : ℕ := a.1.fst.val
  have larger {a b : J × V} (edge : DegreeFirstCutConflict paths D L a b) :
      rank a < rank b := (edge.partner simple).1
  obtain ⟨cover,sub,matching,count,covers,matched⟩ :=
    exists_cut_cover_and_matching (DegreeFirstCutConflict paths D L) rank (fun {_ _} => larger)
      (fun {_ _ _} => DegreeFirstCutConflict.out_unique simple free) support
  exact ⟨cover,sub,matching,count,fun {a b} edge =>
    covers a (mem_pieceIncidences.mpr ⟨mem_univ _,edge.left_mem⟩)
      b (mem_pieceIncidences.mpr ⟨mem_univ _,edge.right_mem⟩) edge,matched⟩

/-- When every matching of actual cut conflicts has at most 37 percent
of the original mass, the degree-first construction meets both budgets
and all four frozen caps at half cutoff five. -/
theorem regularization_list_frozen_half_five_of_degree_first_matching_bound {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (bound : let M := ∑ i, (paths i).length
      let D := 4*M/n
      let L := 4*M/p
      ∀ matching, CutMatching (DegreeFirstCutConflict paths D L)
        (pieceIncidences (listRegularizedPaths paths D L) univ) matching → 100*matching.card ≤ 37*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  obtain ⟨cover,sub,matching,count,covering,good⟩ :=
    degreeFirstCut_cover_and_matching paths simple free (4*M/n) (4*M/p)
  exact regularization_list_frozen_half_five_of_degree_first_cover paths simple free hn hp dense long
    ⟨cover,sub,count.symm ▸ bound matching good,fun {_ _} => covering⟩

end OnlineReachabilityPreservers
