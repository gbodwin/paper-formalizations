import OnlineReachabilityPreservers.FrozenHalfFourConflicts
import OnlineReachabilityPreservers.FrozenLengthCappedPaths
import OnlineReachabilityPreservers.LocalFrozenLowMass

/-! Frozen-average cleaning for unrestricted simple half-four-free path systems. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

private theorem trimmed_mass_mono {M a K c : ℝ} (positive : 0 < M) (lower : a ≤ K)
    (upper : K ≤ M) (wide : 2 ≤ c) :
    a-a^2/(c*M) ≤ K-K^2/(c*M) := by
  have cPos : 0 < c := by linarith
  have room : 0 ≤ c*M-(K+a) := by
    have raw := mul_nonneg (show 0 ≤ c-2 by linarith) positive.le
    nlinarith only [raw,lower,upper]
  have diff : 0 ≤ (K-a)*(c*M-(K+a))/(c*M) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr lower) room) (mul_nonneg cPos.le positive.le)
  have equal : (K-K^2/(c*M))-(a-a^2/(c*M)) = (K-a)*(c*M-(K+a))/(c*M) := by
    field_simp [positive.ne',cPos.ne']
    ring
  rw [← equal] at diff
  exact sub_nonneg.mp diff

private theorem nested_repair_full_retention {M K : ℝ} (positive : 0 < M) (mass : 337*M ≤ 650*K)
    (upper : K ≤ M) :
    M/5000 ≤ K-K^2/((31/2)*M)-M/2 := by
  let a := 337*M/650
  have lower : a ≤ K := by dsimp [a]; linarith only [mass]
  have mono := trimmed_mass_mono positive lower upper (show (2:ℝ) ≤ 31/2 by norm_num)
  have margin : a-a^2/((31/2)*M)-M/2 = 7331*M/6548750 := by
    dsimp [a]
    field_simp [positive.ne']
    ring
  linarith only [mono,margin,positive.le]

private theorem nested_repair_heavy_retention {M K Q : ℝ} (positive : 0 < M) (mass : 3*M ≤ 10*K)
    (upper : K ≤ M) (fee : Q ≤ 34*M/775) :
    M/5000 ≤ K-K^2/((31/2)*M)-M/4-Q := by
  let a := 3*M/10
  have lower : a ≤ K := by dsimp [a]; linarith only [mass]
  have mono := trimmed_mass_mono positive lower upper (show (2:ℝ) ≤ 31/2 by norm_num)
  have margin : a-a^2/((31/2)*M)-M/4-34*M/775 = M/3100 := by
    dsimp [a]
    field_simp [positive.ne']
    ring
  linarith only [mono,margin,positive.le,fee]

private theorem nested_repair_overlong_retention {M S T K : ℝ} (positive : 0 < M)
    (highS : 29*M ≤ 50*S) (highT : 12*M ≤ 25*T) (Supper : S ≤ M)
    (kept : S ≤ 2*K) (Kupper : K ≤ M) :
    M/5000 ≤ K-K^2/(12*M)-M/4-((S-T)/12+K/12) := by
  let a := S/2
  let b := 29*M/50
  have lower : a ≤ K := by dsimp [a]; linarith only [kept]
  have enough : b ≤ S := by dsimp [b]; linarith only [highS]
  have firstRoom : 0 ≤ 11*M-(K+a) := by dsimp [a]; linarith only [Kupper,Supper,positive.le]
  have secondRoom : 0 ≤ 18*M-S-b := by dsimp [b]; linarith only [Supper,positive.le]
  have first := mul_nonneg (sub_nonneg.mpr lower) firstRoom
  have second := mul_nonneg (sub_nonneg.mpr enough) secondRoom
  have firstBound : 11*a/12-a^2/(12*M) ≤ 11*K/12-K^2/(12*M) := by
    have normal : (11*K/12-K^2/(12*M))-(11*a/12-a^2/(12*M)) =
        (K-a)*(11*M-(K+a))/(12*M) := by
      field_simp [positive.ne']
      ring
    apply sub_nonneg.mp
    rw [normal]
    exact div_nonneg first (by positivity)
  have secondBound : 3*b/8-b^2/(48*M) ≤ 3*S/8-S^2/(48*M) := by
    have normal : (3*S/8-S^2/(48*M))-(3*b/8-b^2/(48*M)) =
        (S-b)*(18*M-S-b)/(48*M) := by
      field_simp [positive.ne']
      ring
    apply sub_nonneg.mp
    rw [normal]
    exact div_nonneg second (by positivity)
  have compare : 11*a/12-a^2/(12*M)-M/4-((S-T)/12) = 3*S/8-S^2/(48*M)-M/4+T/12 := by
    dsimp [a]
    field_simp [positive.ne']
    ring
  have margin : 3*b/8-b^2/(48*M)-M/4+(12*M/25)/12 = 59*M/120000 := by
    dsimp [b]
    field_simp [positive.ne']
    ring
  linarith only [firstBound,secondBound,compare,margin,highT,positive.le]

section RowBlocks

variable {n p : ℕ}

private def heavyRows (paths : Fin p → List (Fin n)) (width : ℕ) : Finset (Fin p) :=
  univ.filter fun i => width < (paths i).length

private def heavyPieces (paths : Fin p → List (Fin n)) (width : ℕ) : Finset (ListBlockIndex paths width) :=
  univ.filter fun i => width < (paths i.fst).length

private def lightPieces (paths : Fin p → List (Fin n)) (width : ℕ) : Finset (ListBlockIndex paths width) :=
  univ.filter fun i => (paths i.fst).length ≤ width ∧ i.snd.val = 0

private theorem same_path_block {paths : Fin p → List (Fin n)} {width : ℕ} {a b : ListBlockIndex paths width}
    (row : a.fst = b.fst) (index : a.snd.val = b.snd.val) : a = b := by
  rcases a with ⟨i,s⟩
  rcases b with ⟨j,t⟩
  change i = j at row
  subst j
  obtain rfl := Fin.ext index
  rfl

private theorem short_block_zero {paths : Fin p → List (Fin n)} {width : ℕ} {i : ListBlockIndex paths width}
    (small : (paths i.fst).length ≤ width) {v : Fin n} (occurs : v ∈ splitListPaths paths width i) :
    i.snd.val = 0 := by
  obtain ⟨original,eq⟩ := mem_localPathBlock.mp occurs
  rw [← eq]
  exact Nat.div_eq_of_lt ((List.idxOf_lt_length_of_mem original).trans_le small)

private theorem lightPieces_count {paths : Fin p → List (Fin n)} {width : ℕ} :
    (lightPieces paths width).card ≤ p-(heavyRows paths width).card := by
  have count : (lightPieces paths width).card ≤ (univ \ heavyRows paths width).card := by
    apply card_le_card_of_injOn (fun j : ListBlockIndex paths width => j.fst)
    · intro i member
      have le := (mem_filter.mp member).2.1
      exact mem_sdiff.mpr ⟨mem_univ _,fun heavy => (not_lt_of_ge le) (mem_filter.mp heavy).2⟩
    · intro a onA b onB same
      exact same_path_block same ((mem_filter.mp onA).2.2.trans (mem_filter.mp onB).2.2.symm)
  have parts := card_sdiff_add_card_eq_card (subset_univ (heavyRows paths width))
  rw [card_univ,Fintype.card_fin] at parts
  omega

private theorem sum_heavyPieces (paths : Fin p → List (Fin n)) (width : ℕ)
    (weight : ListBlockIndex paths width → ℕ) :
    (∑ j ∈ heavyPieces paths width, weight j) =
      ∑ i ∈ heavyRows paths width, ∑ b : Fin (blockCount (paths i).toFinset width), weight ⟨i,b⟩ := by
  unfold heavyPieces heavyRows
  rw [sum_filter,sum_filter]
  change (∑ j : (Σ i : Fin p, Fin (blockCount (paths i).toFinset width)),
    if width < (paths j.fst).length then weight j else 0) = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  by_cases h : width < (paths i).length <;> simp [h]

private theorem heavyPieces_mass {paths : Fin p → List (Fin n)} (simple : ∀ i, (paths i).Nodup) (width : ℕ) :
    (∑ j ∈ heavyPieces paths width, (splitListPaths paths width j).length) = listMassAboveWidth paths width := by
  rw [sum_heavyPieces]
  exact sum_congr rfl fun i _ => localPathBlock_sum (paths i) (simple i) width

private theorem heavyPieces_width {paths : Fin p → List (Fin n)} (simple : ∀ i, (paths i).Nodup) (width : ℕ) :
    width*(heavyPieces paths width).card ≤ (heavyRows paths width).card*width+listMassAboveWidth paths width := by
  let H := heavyRows paths width
  have count : (heavyPieces paths width).card = ∑ i ∈ H, ((paths i).length/width+1) := by
    rw [show (heavyPieces paths width).card = ∑ _ ∈ heavyPieces paths width, (1:ℕ) by simp,
      sum_heavyPieces]
    refine sum_congr rfl fun i _ => ?_
    change (∑ _ : Fin (blockCount (paths i).toFinset width), (1:ℕ)) = _
    rw [← Fintype.card_eq_sum_ones,Fintype.card_fin,blockCount,List.toFinset_card_of_nodup (simple i)]
  calc
    _ = ∑ i ∈ H, width*((paths i).length/width+1) := by rw [count,mul_sum]
    _ ≤ ∑ i ∈ H, (width+(paths i).length) := by
      apply sum_le_sum
      intro i _
      have floor := Nat.div_mul_le_self (paths i).length width
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm width]
      omega
    _ = _ := by rw [sum_add_distrib]; simp [H,heavyRows,listMassAboveWidth]

private theorem splitPath_step {paths : Fin p → List (Fin n)} (simple : ∀ i, (paths i).Nodup) {width : ℕ}
    {i : ListBlockIndex paths width} {x y : Fin n} (step : Before (splitListPaths paths width) i x y) :
    Before paths i.fst x y :=
  listBefore_of_sublist (paths := fun j : ListBlockIndex paths width => paths j.fst)
    (cut := splitListPaths paths width) (simple i.fst) List.filter_sublist step

private theorem heavyPieces_contain_sources {paths : Fin p → List (Fin n)} (width : ℕ) :
    nestedCutSources paths (splitListPaths paths width) Sigma.fst ⊆
      pieceIncidences (splitListPaths paths width) (heavyPieces paths width) := by
  classical
  intro a member
  obtain ⟨b,edge⟩ := (mem_filter.mp member).2
  refine mem_pieceIncidences.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,edge.left_mem⟩
  obtain ⟨_,early,_,_,_,_,different,same,_,_,_,_,first,last,_,_⟩ := edge
  by_contra h
  have short : (paths a.1.fst).length ≤ width := Nat.le_of_not_gt h
  have earlyShort : (paths early.fst).length ≤ width := same.symm ▸ short
  exact different (same_path_block same
    ((short_block_zero earlyShort first.1).trans (short_block_zero short last.1).symm))

private theorem dense_width_product {M q : ℕ} (positive : 0 < q) (dense : 8*q ≤ M) :
    31*M ≤ 8*((4*M/q)*q) := by
  have near := four_average_width_product positive (M := M)
  omega

private theorem half_four_budget_loss {n M K : ℕ} (positive : 0 < M) (room : 31*M ≤ 8*((4*M/n)*n)) :
    (K:ℝ)^2/(4*((4*M/n*n : ℕ):ℝ)) ≤ (K:ℝ)^2/((31/2)*(M:ℝ)) := by
  have roomReal : 31*(M:ℝ) ≤ 8*((4*M/n*n : ℕ):ℝ) := by exact_mod_cast room
  have positiveReal : (0:ℝ) < M := by exact_mod_cast positive
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  linarith

private theorem half_four_path_charge {p M Q : ℕ} (hp : 0 < p) {a b : ℝ} (bPos : 0 < b)
    (quota : b*(Q:ℝ) ≤ a*(p:ℝ)) :
    (M:ℝ)/(4*(p:ℝ))*(Q:ℝ) ≤ a*(M:ℝ)/(4*b) := by
  have pPos : (0:ℝ) < p := by exact_mod_cast hp
  have scaled := mul_le_mul_of_nonneg_left quota (show (0:ℝ) ≤ M by positivity)
  calc
    _ = ((M:ℝ)*(b*Q))/(4*(p:ℝ)*b) := by field_simp [bPos.ne',pPos.ne']
    _ ≤ ((M:ℝ)*(a*p))/(4*(p:ℝ)*b) := div_le_div_of_nonneg_right scaled (by positivity)
    _ = _ := by field_simp [bPos.ne',pPos.ne']

set_option maxHeartbeats 1200000 in
private theorem half_four_of_moderate_overlong_mass (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 4)
    (hn : 0 < n) (hp : 0 < p)
    (largeN : 8*n ≤ ∑ i, (paths i).length) (largeP : 8*p ≤ ∑ i, (paths i).length)
    (moderate : let M := ∑ i, (paths i).length; 50*listMassAboveWidth paths (4*M/p) ≤ 29*M)
    (excess : let M := ∑ i, (paths i).length; 12*M ≤ 25*listLengthExcess paths (4*M/p)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let S := listMassAboveWidth paths L
  let T := listLengthExcess paths L
  let J := ListBlockIndex paths L
  let pieces := splitListPaths paths L
  let heavy := heavyPieces paths L
  let light := lightPieces paths L
  let q := (heavyRows paths L).card
  let Q := heavy.card
  have dense : n ≤ M := by change 8*n ≤ M at largeN; omega
  have long : p ≤ M := by change 8*p ≤ M at largeP; omega
  have positive : 0 < M := hn.trans_le dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  have vRoom := dense_width_product hn largeN
  have pRoom : 31*M ≤ 8*(L*p) := dense_width_product hp largeP
  have pieceSimple (i : J) : (pieces i).Nodup := List.filter_sublist.nodup (simple i.fst)
  have steps {i : J} {x y : Fin n} : Before pieces i x y → Before paths i.fst x y := splitPath_step simple
  have apart {i j : J} {x : Fin n} :
      i ≠ j → i.fst = j.fst → x ∈ pieces i → x ∈ pieces j → False := splitListPaths_disjoint
  have total : (∑ i : J, (pieces i).length) = M := splitListPaths_size paths simple L
  have heavyMass : (∑ i ∈ heavy, (pieces i).length) = S := heavyPieces_mass simple L
  have separate : Disjoint heavy light := disjoint_left.mpr fun _ h l =>
    (not_lt_of_ge (mem_filter.mp l).2.1) (mem_filter.mp h).2
  have covers (i : J) (nonempty : pieces i ≠ []) : i ∈ heavy ∪ light := by
    by_cases h : L < (paths i.fst).length
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    · have short := Nat.le_of_not_gt h
      have zero : i.snd.val = 0 := by
        cases eq : pieces i with
        | nil => exact (nonempty eq).elim
        | cons v rest =>
          apply short_block_zero short (v := v)
          change v ∈ pieces i
          rw [eq]
          exact List.mem_cons_self
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,short,zero⟩)
  have widths : L*Q ≤ q*L+S := heavyPieces_width simple L
  have tails : T+q*L = S := listLengthExcess_add_count_mul paths L
  change 50*S ≤ 29*M at moderate
  change 12*M ≤ 25*T at excess
  have sparseHeavy : 25*(L*Q) ≤ 17*M := by omega
  have heavyCap : 775*Q ≤ 136*p := by
    apply Nat.le_of_mul_le_mul_right _ positive
    calc
      (775*Q)*M = (25*Q)*(31*M) := by ring
      _ ≤ (25*Q)*(8*(L*p)) := Nat.mul_le_mul_left _ pRoom
      _ = (8*p)*(25*(L*Q)) := by ring
      _ ≤ (8*p)*(17*M) := Nat.mul_le_mul_left _ sparseHeavy
      _ = (136*p)*M := by ring
  have heavyFits : Q ≤ p := by omega
  have lightCount : light.card ≤ p-q := lightPieces_count
  have qBound : 13*Q ≤ 2*p+11*q := by
    apply Nat.le_of_mul_le_mul_left _ lPos
    calc
      L*(13*Q) = 13*(L*Q) := by ring
      _ ≤ 2*(L*p)+11*(q*L) := by omega
      _ = L*(2*p+11*q) := by ring
  have lightRoom : 11*light.card ≤ 13*(p-Q) := by omega
  have hyp : 50*(∑ i ∈ heavy, (pieces i).length) ≤ 29*(∑ i : J, (pieces i).length) := by
    rw [heavyMass,total]
    exact moderate
  obtain ⟨deleted,kept,coverCut,countK,big⟩ := nestedCut_repair_budget free pieceSimple (fun {_ _ _} => steps)
    (fun {_ _ _} => apart) heavy light separate covers (heavyPieces_contain_sources L) heavyFits lightRoom hyp
  let filtered := erasePieceIncidences pieces deleted
  let rows (i : kept) := filtered i.val
  have filteredFree : HalfBridgeFree (Before filtered) 4 := by
    exact erasePieceIncidences_halfFree free pieceSimple (block_parent_mono (fun i => (paths i).toFinset) L)
      (fun {_ _ _} => steps) (fun {_ _ _} => apart) (fun {_ _} => listBlocks_ordered paths L)
      deleted (fun {_ _} => coverCut)
  have rowFree : HalfBridgeFree (Before rows) 4 := by
    intro j short bridge arrives
    exact filteredFree short (bridge.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ h => h)) arrives
  have rowSimple (i : kept) : (rows i).Nodup :=
    (erasePieceIncidences_sublist pieces deleted i.val).nodup (pieceSimple i.val)
  have rowWidth (i : kept) : (rows i).length ≤ L :=
    (erasePieceIncidences_sublist pieces deleted i.val).length_le.trans
      (localPathBlock_length _ (simple i.val.fst) lPos _)
  let K := ∑ i : kept, (rows i).length
  have massK : K = ∑ i ∈ kept, (filtered i).length := by simpa [K,rows] using sum_attach kept (fun i => (filtered i).length)
  have upper : K ≤ M := calc
    _ = ∑ i ∈ kept, (filtered i).length := massK
    _ ≤ ∑ i ∈ kept, (pieces i).length := sum_le_sum fun i _ => (erasePieceIncidences_sublist pieces deleted i).length_le
    _ ≤ ∑ i : J, (pieces i).length := sum_le_sum_of_subset (subset_univ _)
    _ = _ := total
  rw [total,← massK] at big
  refine regularization_list_frozen_of_length_capped_exact_budget (half := true) (k := 4) rows
    rowSimple rowFree (fun _ => le_rfl) hn hp dense long (by simpa using countK) rowWidth upper (by decide) ?_
  have realPos : (0:ℝ) < M := by exact_mod_cast positive
  have realUpper : (K:ℝ) ≤ M := by exact_mod_cast upper
  have vertexLoss := half_four_budget_loss (K := K) positive vRoom
  change (M:ℝ)/5000 ≤ (K:ℝ)-(K:ℝ)^2/(4*((4*M/n*n : ℕ):ℝ))-(M:ℝ)/4-(M:ℝ)/(4*(p:ℝ))*(Fintype.card kept:ℝ)
  rw [Fintype.card_coe]
  rcases big with ⟨eq,heavyLower⟩ | lower
  · have fee := half_four_path_charge (Q := kept.card) (M := M) hp (a := 136) (b := 775)
      (by norm_num) (by rw [eq]; exact_mod_cast heavyCap)
    have loss : (M:ℝ)/(4*(p:ℝ))*(kept.card:ℝ) ≤ 34*(M:ℝ)/775 := by linarith only [fee]
    have keep := nested_repair_heavy_retention realPos (by exact_mod_cast heavyLower) realUpper loss
    linarith only [keep,vertexLoss]
  · have fee := half_four_path_charge (Q := kept.card) (M := M) hp (a := 1) (b := 1)
      (by norm_num) (by simpa only [one_mul] using (Nat.cast_le.mpr countK : (kept.card:ℝ) ≤ p))
    have keep := nested_repair_full_retention realPos (by exact_mod_cast lower) realUpper
    linarith only [keep,fee,vertexLoss]

/-- Every simple half-four-free family whose mass reaches both original budgets
has a half-four-free witness with both budgets and all four original-average caps. -/
theorem regularization_list_frozen_half_four (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let T := listLengthExcess paths L
  let S := listMassAboveWidth paths L
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vCap,q,qCap,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨v,vCap,q,qCap,clean,cleanSimple,(fun _ small => cleanFree.halfFree small),
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  have largeN : 8*n ≤ M := (Nat.mul_le_mul_left _ (le_max_left _ _)).trans (le_of_not_ge low)
  have largeP : 8*p ≤ M := (Nat.mul_le_mul_left _ (le_max_right _ _)).trans (le_of_not_ge low)
  have positive : 0 < M := hn.trans_le dense
  have realPos : (0:ℝ) < M := by exact_mod_cast positive
  by_cases small : 25*T ≤ 12*M
  · let clipped (i : Fin p) := (paths i).take L
    let K := ∑ i, (clipped i).length
    have sub (i : Fin p) : (clipped i).Sublist (paths i) := List.take_sublist _ _
    have clipFree : HalfBridgeFree (Before clipped) 4 := by
      intro r short bridge arrives
      exact free short (bridge.mapPaths id Function.injective_id
        (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step)) arrives
    have lengths : K+T = M := by
      unfold K T listLengthExcess M
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      rw [show (clipped i).length = min L (paths i).length from List.length_take]
      omega
    have upper : K ≤ M := by omega
    have lower : 337*M ≤ 650*K := by omega
    have clipWidth (i : Fin p) : (clipped i).length ≤ L := by
      change ((paths i).take L).length ≤ L
      rw [List.length_take]
      exact min_le_left _ _
    refine regularization_list_frozen_of_length_capped_exact_budget (half := true) (k := 4) clipped
      (fun i => (sub i).nodup (simple i)) clipFree (fun _ => le_rfl) hn hp dense long (by simp)
      clipWidth upper (by decide) ?_
    have vertexLoss := half_four_budget_loss (K := K) positive (dense_width_product hn largeN)
    have pathLoss := half_four_path_charge (Q := p) (M := M) hp (a := 1) (b := 1) (by norm_num) le_rfl
    have keep := nested_repair_full_retention (K := (K:ℝ)) realPos
      (by exact_mod_cast lower) (by exact_mod_cast upper)
    change (M:ℝ)/5000 ≤ (K:ℝ)-(K:ℝ)^2/(4*((4*M/n*n : ℕ):ℝ))-(M:ℝ)/4-(M:ℝ)/(4*(p:ℝ))*(Fintype.card (Fin p):ℝ)
    rw [Fintype.card_fin]
    linarith only [keep,pathLoss,vertexLoss]
  have excess : 12*M ≤ 25*T := le_of_not_ge small
  by_cases large : 29*M ≤ 50*S
  · refine regularization_list_frozen_from_overlong_budget (retention := 5000) true paths simple free hn hp
      dense long (by decide) ?_
    dsimp only
    intro K lower upper
    have sUpper : S ≤ M := sum_le_sum_of_subset (subset_univ (heavyRows paths L))
    have keep := nested_repair_overlong_retention (M := (M:ℝ)) (S := (S:ℝ)) (T := (T:ℝ)) (K := (K:ℝ))
      realPos (by exact_mod_cast large) (by exact_mod_cast excess) (by exact_mod_cast sUpper)
      (by exact_mod_cast lower) (by exact_mod_cast upper)
    change (M:ℝ)/5000 ≤ (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-
      (min ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)+(K:ℝ)/12)
    linarith only [keep,min_le_right ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)]
  exact half_four_of_moderate_overlong_mass paths simple free hn hp largeN largeP (le_of_not_ge large) excess

/-- At half cutoff four, a constant fraction of the unrestricted maximum
fits both budgets and all four original-average caps. -/
theorem localOrderExtremal_frozen_half_four (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 4 ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → HalfBridgeFree (Before other) 4 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
        M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p 4 true hn hp
  exact ⟨paths,simple,free,maximal,regularization_list_frozen_half_four paths simple free hn hp dense long⟩

end RowBlocks

end OnlineReachabilityPreservers
