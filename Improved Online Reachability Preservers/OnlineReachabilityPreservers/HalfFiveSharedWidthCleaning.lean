import OnlineReachabilityPreservers.HalfFivePathCleaning

/-! Repair both length and degree width splits with one color deletion. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

/-- The incidences involved in an opposite comparison across a row cut,
together with all incidences at an originally overfull vertex. -/
noncomputable def sharedWidthAffected {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) :
    Finset (ListBlockIndex paths L × Fin n) :=
  let raw := splitListPaths paths L
  oppositeWidthConflictIncidences paths raw Sigma.fst ∪
    (pieceIncidences raw univ).filter fun x =>
      D < (occurrences (fun i => (paths i).toFinset) x.2).card

/-- Delete one reverse-partner color on the union of the two affected sets. -/
noncomputable def sharedWidthDeletion {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) (c : Bool) :
    Finset (ListBlockIndex paths L × Fin n) :=
  (sharedWidthAffected paths D L).filter fun x => reversePartnerColor paths x.2 x.1.fst = c

/-- A single color deletion suffices for both consecutive width splits
through half cutoff five. -/
theorem sharedWidthRepair_halfFree {n p : ℕ} (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (D L : ℕ) (c : Bool) :
    HalfBridgeFree (Before (splitListVertices
      (erasePieceIncidences (splitListPaths paths L) (sharedWidthDeletion paths D L c)) D)) 5 := by
  let J := ListBlockIndex paths L
  let raw := splitListPaths paths L
  let parent (j : J) := j.fst
  let marks := fun i => (paths i).toFinset
  let remove := sharedWidthDeletion paths D L c
  let rows := erasePieceIncidences raw remove
  have rawSimple (j : J) : (raw j).Nodup := List.filter_sublist.nodup (simple j.fst)
  have rawSub (j : J) : (raw j).Sublist (paths j.fst) := List.filter_sublist
  have originalStep {j x y} : Before raw j x y → Before paths (parent j) x y :=
    listBefore_of_sublist (paths := fun j : J => paths j.fst) (simple j.fst) (rawSub j)
  have apart {j j' : J} {x : Fin n} :
      j ≠ j' → parent j = parent j' → x ∈ raw j → x ∈ raw j' → False := splitListPaths_disjoint
  have monotone : Monotone parent := block_parent_mono marks L
  have cover {a b} (edge : OppositeWidthConflict paths raw parent a b) : a ∈ remove ∨ b ∈ remove := by
    have included : oppositeWidthDeletion paths raw parent c ⊆ remove := by
      intro x involved
      obtain ⟨member,color⟩ := mem_filter.mp involved
      exact mem_filter.mpr ⟨mem_union_left _ member,color⟩
    exact (oppositeWidthDeletion_covers free (by decide) (fun {_ _ _} => originalStep) edge c).imp (fun hx => included hx) (fun hx => included hx)
  have rowFree : HalfBridgeFree (Before rows) 5 :=
    eraseOppositeWidthConflicts_halfFree free rawSimple monotone (fun {_ _ _} => originalStep)
      (fun {_ _ _} => apart) remove (fun {_ _} => cover)
  have rowSimple (j : J) : (rows j).Nodup :=
    (erasePieceIncidences_sublist raw remove j).nodup (rawSimple j)
  have rawMem {j : J} {x : Fin n} (incidence : x ∈ rows j) : x ∈ raw j :=
    (mem_erasePieceIncidences.mp incidence).1
  have noIncrease (x : Fin n) : (occurrences (fun j => (rows j).toFinset) x).card ≤
      (occurrences marks x).card := by
    have membership {j : J} (jOn : j ∈ occurrences (fun k => (rows k).toFinset) x) :
        x ∈ raw j := rawMem (List.mem_toFinset.mp ((mem_occurrences (marks := fun k => (rows k).toFinset)).mp jOn))
    apply card_le_card_of_injOn parent
    · intro j on
      exact mem_occurrences.mpr (List.mem_toFinset.mpr ((rawSub j).subset (membership on)))
    · intro j hj k hk same
      by_contra different
      exact apart different same (membership hj) (membership hk)
  have selected {x : Fin n} {i : J} (heavy : D < (occurrences (fun j => (rows j).toFinset) x).card)
      (onRow : x ∈ rows i) : reversePartnerColor paths x (parent i) = !c := by
    have high : D < (occurrences marks x).card := heavy.trans_le (noIncrease x)
    have on : (i,x) ∈ pieceIncidences raw univ := mem_pieceIncidences.mpr ⟨mem_univ _,rawMem onRow⟩
    have involved : (i,x) ∈ sharedWidthAffected paths D L := mem_union_right _ (mem_filter.mpr ⟨on,high⟩)
    have different : reversePartnerColor paths x (parent i) ≠ c := by
      intro equal
      exact (mem_erasePieceIncidences.mp onRow).2 (mem_filter.mpr ⟨involved,equal⟩)
    cases c <;> cases eq : reversePartnerColor paths x (parent i) <;> simp_all
  refine splitListVertices_halfFive_of_original_colors paths rows parent free rowFree rowSimple monotone
    ?_ (fun ne eq left right => apart ne eq (rawMem left) (rawMem right)) D (fun _ => !c)
    (fun {_ _} => selected)
  intro i x y step
  exact originalStep (listBefore_of_sublist (rawSimple i) (erasePieceIncidences_sublist raw remove i) step)

private theorem sharedWidth_final_budget {M K R Y X C : ℕ} (positive : 0 < M)
    (high : 3*M ≤ 5*K) (upper : K ≤ M) (retained : K ≤ R+Y+X)
    (rowLoss : 31*Y ≤ 2*M) (capacity : 31*M ≤ 8*C) (vertexLoss : 4*C*X ≤ K^2) :
    5002*M ≤ 10000*R := by
  have vertex : 31*M*X ≤ 2*K^2 := calc
    _ ≤ (8*C)*X := Nat.mul_le_mul_right _ capacity
    _ = 2*(4*C*X) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ vertexLoss
  have row : 31*M*Y ≤ 2*M^2 := calc
    _ = (31*Y)*M := by ring
    _ ≤ (2*M)*M := Nat.mul_le_mul_right _ rowLoss
    _ = _ := by ring
  have paid : 31*M*K ≤ 31*M*R+2*M^2+2*K^2 := calc
    _ ≤ 31*M*(R+Y+X) := Nat.mul_le_mul_left _ retained
    _ = 31*M*R+31*M*Y+31*M*X := by ring
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add_left row _) vertex
  have paidReal : 31*(M:ℝ)*K ≤ 31*(M:ℝ)*R+2*(M:ℝ)^2+2*(K:ℝ)^2 := by exact_mod_cast paid
  have lower : 0 ≤ (K:ℝ)-3*(M:ℝ)/5 := by
    have h : 3*(M:ℝ) ≤ 5*(K:ℝ) := by exact_mod_cast high
    linarith
  have room : 0 ≤ 31*(M:ℝ)-2*((K:ℝ)+3*(M:ℝ)/5) := by
    have h : (K:ℝ) ≤ M := by exact_mod_cast upper
    linarith [Nat.cast_nonneg (α := ℝ) M]
  have enough : (5002*(M:ℝ))*M ≤ (10000*(R:ℝ))*M := by
    nlinarith only [paidReal,mul_nonneg lower room,sq_nonneg (M:ℝ)]
  apply (Nat.mul_le_mul_right_iff positive).mp
  exact_mod_cast enough

/-- When the union of the affected incidences of both width splits uses
at most four fifths of the mass, one color deletion suffices at half five. -/
theorem regularization_list_frozen_half_five_of_shared_width_budget {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (bound : let M := ∑ i, (paths i).length; 5*(sharedWidthAffected paths (4*M/n) (4*M/p)).card ≤ 4*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',hn',p',hp',clean,cleanSimple,legal,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨n',hn',p',hp',clean,cleanSimple,fun _ small b _ => (legal small).false b,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  let J := ListBlockIndex paths L
  let raw := splitListPaths paths L
  let affected := sharedWidthAffected paths D L
  have nDense : 8*n ≤ M := by have h := le_max_left n p; omega
  have pDense : 8*p ≤ M := by have h := le_max_right n p; omega
  have capacity : 31*M ≤ 8*(D*n) := by
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  have dPos : 0 < D := (four_average_width hn dense).1
  have lPos : 0 < L := (four_average_width hp long).1
  have rawLength (j : J) : (raw j).length ≤ L := localPathBlock_length _ (simple j.fst) lPos j.snd.val
  have rawSimple (j : J) : (raw j).Nodup := List.filter_sublist.nodup (simple j.fst)
  have rawMass : (∑ j : J, (raw j).length) = M := splitListPaths_size paths simple L
  obtain ⟨B,rowBudget,rowLoss⟩ := trimSplitListPaths_at_original_width paths simple hp pDense
  obtain ⟨c,deleteBound⟩ := exists_smallBoolColor affected
    (fun a => reversePartnerColor paths a.2 a.1.fst)
  let deleted := sharedWidthDeletion paths D L c
  let rows := erasePieceIncidences raw deleted
  let K := ∑ j, (rows j).length
  let Y := ∑ j ∈ univ \ B, (raw j).length
  let pieces := splitListVertices rows D
  let Z (j : J) := (pieces j).toFinset
  have exactLoss : K+(pieceIncidences raw univ ∩ deleted).card = M :=
    (erasePieceIncidences_mass_add_loss rawSimple univ deleted).trans rawMass
  have lost : (pieceIncidences raw univ ∩ deleted).card ≤ deleted.card := card_le_card inter_subset_right
  have deleteBound' : 2*deleted.card ≤ affected.card := deleteBound
  change 5*affected.card ≤ 4*M at bound
  have large : 3*M ≤ 5*K := by omega
  have upper : K ≤ M := by omega
  have rowSimple (j : J) : (rows j).Nodup :=
    (erasePieceIncidences_sublist raw deleted j).nodup (rawSimple j)
  have pieceSimple (j : J) : (pieces j).Nodup := splitListVertices_simple rows D j (rowSimple j)
  have piecesFree := sharedWidthRepair_halfFree paths simple free D L c
  have pieceLength (j : J) : (pieces j).length ≤ L :=
    (splitListVertices_length rows D j).trans_le
      ((erasePieceIncidences_sublist raw deleted j).length_le.trans (rawLength j))
  have setMass : (∑ j : J, (Z j).card) = K := by
    apply sum_congr rfl
    intro j _
    exact (List.toFinset_card_of_nodup (pieceSimple j)).trans (splitListVertices_length rows D j)
  have degree (v : ListVertexBlockIndex rows D) : (occurrences Z v).card ≤ D := by
    rw [show Z = splitVertices (fun i => (rows i).toFinset) D from funext (splitListVertices_toFinset rows D)]
    exact splitVertices_degree _ dPos v
  obtain ⟨filled,filledDegree,remainder⟩ := splitListVertices_full_block_profile rows dPos
  have rem : (univ \ filled).card ≤ n := by simpa only [Fintype.card_fin] using remainder.le
  have room : (∑ j, (Z j).card) ≤ D*n := by rw [setMass]; omega
  obtain ⟨A,vertexBudget,X,vertexLoss,vertexExact⟩ :=
    trim_full_vertex_blocks_quadratic Z filled dPos filledDegree rem room
  rw [setMass] at vertexLoss vertexExact
  let clean := restrictListPaths pieces A B
  have cleanSimple (j : B) : (clean j).Nodup := restrictListPath_nodup (pieceSimple j.val) A
  have cleanFree : HalfBridgeFree (Before clean) 5 := restrictListPaths_halfFree pieceSimple piecesFree A B
  have cleanLength (j : B) : (clean j).length ≤ L := by
    rw [show (clean j).length = (Z j.val ∩ A).card from restrictListPath_length (pieceSimple j.val) A]
    exact (card_le_card inter_subset_left).trans ((List.toFinset_card_le _).trans (pieceLength j.val))
  have cleanDegree (v : A) : (occurrences (fun j => (clean j).toFinset) v).card ≤ D := by
    rw [show (fun j => (clean j).toFinset) = rectanglePaths Z A B from funext (restrictListPaths_toFinset pieces A B)]
    exact (rectanglePaths_degree_le Z A B v).trans (degree v.val)
  let R := ∑ j : B, (clean j).length
  have cleanCount : R = ∑ j ∈ B, (Z j ∩ A).card := by
    rw [show R = ∑ j ∈ B.attach, (Z j.val ∩ A).card from
      sum_congr rfl (fun j _ => restrictListPath_length (pieceSimple j.val) A)]
    exact sum_attach B (fun j => (Z j ∩ A).card)
  have croppedVertex : ∑ j : (univ : Finset J), (rectanglePaths Z A univ j).card =
      ∑ j : J, (Z j ∩ A).card := by
    rw [Finset.sum_subtype (univ : Finset J) (fun _ => Iff.rfl) (fun i => (Z i ∩ A).card)]
    apply sum_congr rfl
    intro j _
    calc
      _ = ((restrictListPaths pieces A univ j).toFinset).card :=
        (congrArg Finset.card (restrictListPaths_toFinset pieces A univ j)).symm
      _ = (restrictListPaths pieces A univ j).length :=
        List.toFinset_card_of_nodup (restrictListPath_nodup (pieceSimple j.val) A)
      _ = _ := restrictListPath_length (pieceSimple j.val) A
  rw [croppedVertex] at vertexExact
  have clippedRow : (∑ j ∈ univ \ B, (Z j ∩ A).card) ≤ Y := by
    apply sum_le_sum
    intro j _
    calc
      _ ≤ (Z j).card := card_le_card inter_subset_left
      _ ≤ (pieces j).length := List.toFinset_card_le _
      _ = (rows j).length := splitListVertices_length rows D j
      _ ≤ _ := (erasePieceIncidences_sublist raw deleted j).length_le
  have byRows : (∑ j : J, (Z j ∩ A).card) ≤ R+Y := by
    rw [← sum_sdiff (subset_univ B), ← cleanCount]
    exact (Nat.add_le_add_right clippedRow _).trans_eq (Nat.add_comm _ _)
  have retained : K ≤ R+Y+X := vertexExact.ge.trans (Nat.add_le_add_right byRows _)
  have upperR : R ≤ M := by
    rw [cleanCount]
    exact (sum_le_sum (fun j _ => card_le_card inter_subset_left)).trans
      ((sum_le_sum_of_subset (subset_univ B)).trans (setMass.trans_le upper))
  have cost : 5002*M ≤ 10000*R :=
    sharedWidth_final_budget (hn.trans_le dense) large upper retained rowLoss capacity vertexLoss
  apply regularization_list_frozen_after_caps_with_ratios_of_mass (half := true) (k := 5) (retention := 5000)
    (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1)
    clean cleanSimple cleanFree hn hp dense long (by decide) (by decide) le_rfl le_rfl
    (by simpa only [one_mul,Fintype.card_coe] using vertexBudget)
    (by simpa only [one_mul,Fintype.card_coe] using rowBudget) cleanLength cleanDegree upperR
  exact cost

end OnlineReachabilityPreservers
