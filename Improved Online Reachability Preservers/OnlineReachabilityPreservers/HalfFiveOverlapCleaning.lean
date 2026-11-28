import OnlineReachabilityPreservers.FrozenQuadraticTrimming
import OnlineReachabilityPreservers.HalfFiveSparseWidthPacking
import OnlineReachabilityPreservers.LiteralFrozenHalfFive

/-! Pay for opposite-incidence cuts and fit both original budgets. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private theorem restriction_loss_le_global {I V : Type*} [Fintype I] [DecidableEq V]
    (raw repaired : I → List V) (simple : ∀ i, (raw i).Nodup)
    (sub : ∀ i, (repaired i).Sublist (raw i)) (A : Finset V) (B : Finset I) {loss : ℕ}
    (paid : (∑ i, (raw i).length) ≤ (∑ i, (repaired i).length)+loss) :
    (∑ i ∈ B, ((raw i).toFinset ∩ A).card) ≤ (∑ i ∈ B, ((repaired i).toFinset ∩ A).card)+loss := by
  classical
  let original (i : I) := (raw i).toFinset
  let kept (i : I) := (repaired i).toFinset
  have includes (i : I) : kept i ⊆ original i := by
    intro v present
    exact List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp present))
  let erased (i : I) := ((original i) \ (kept i)).card
  let cropped (i : I) := ((original i ∩ A) \ (kept i ∩ A)).card
  have byRow (i : I) : erased i+(repaired i).length = (raw i).length := by
    have count := card_sdiff_add_card_eq_card (includes i)
    simpa only [erased,original,kept,List.toFinset_card_of_nodup (simple i),
      List.toFinset_card_of_nodup ((sub i).nodup (simple i))] using count
  have total : (∑ i, erased i)+(∑ i, (repaired i).length) = ∑ i, (raw i).length := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => byRow i
  have each (i : I) : cropped i ≤ erased i := by
    apply card_le_card
    intro v visible
    obtain ⟨on,removed⟩ := mem_sdiff.mp visible
    obtain ⟨somewhere,inA⟩ := mem_inter.mp on
    exact mem_sdiff.mpr ⟨somewhere,fun member => removed (mem_inter.mpr ⟨member,inA⟩)⟩
  have sumCrop : (∑ i ∈ B, cropped i) ≤ ∑ i, erased i :=
    (sum_le_sum fun i _ => each i).trans (sum_le_sum_of_subset (subset_univ B))
  have exactCrop : (∑ i ∈ B, cropped i)+(∑ i ∈ B, (kept i ∩ A).card) = ∑ i ∈ B, (original i ∩ A).card := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => card_sdiff_add_card_eq_card (inter_subset_inter_right (includes i))
  change (∑ i ∈ B, (original i ∩ A).card) ≤ (∑ i ∈ B, (kept i ∩ A).card)+loss
  omega

private theorem half_five_sparse_crop_mass {M K R repaired lostV lostI fee vertexCapacity pathCapacity : ℕ}
    (positive : 0 < M) (lower : 2*M ≤ 3*K) (upper : K ≤ M)
    (crop : K ≤ R+(lostV+lostI)) (cut : R ≤ repaired+fee) (feeBound : 8*fee ≤ K)
    (vertexRoom : 31*M ≤ 8*vertexCapacity) (pathRoom : 31*M ≤ 8*pathCapacity)
    (lossV : 4*vertexCapacity*lostV ≤ K^2) (lossI : 4*pathCapacity*lostI ≤ K^2) :
    587*M ≤ 1116*repaired := by
  have vCost : 31*M*lostV ≤ 2*K^2 := calc
    _ ≤ (8*vertexCapacity)*lostV := Nat.mul_le_mul_right _ vertexRoom
    _ = 2*(4*vertexCapacity*lostV) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ lossV
  have iCost : 31*M*lostI ≤ 2*K^2 := calc
    _ ≤ (8*pathCapacity)*lostI := Nat.mul_le_mul_right _ pathRoom
    _ = 2*(4*pathCapacity*lostI) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ lossI
  have cost : 31*M*K ≤ 31*M*R+4*K^2 := calc
    _ ≤ 31*M*(R+(lostV+lostI)) := Nat.mul_le_mul_left _ crop
    _ = 31*M*R+(31*M*lostV+31*M*lostI) := by ring
    _ ≤ _ := by have combined := add_le_add vCost iCost; omega
  have cropReal : 31*(M:ℝ)*K ≤ 31*(M:ℝ)*R+4*(K:ℝ)^2 := by exact_mod_cast cost
  have paidCut : (R:ℝ) ≤ (repaired:ℝ)+fee := by exact_mod_cast cut
  have paidFee : 8*(fee:ℝ) ≤ K := by exact_mod_cast feeBound
  have factor : (0:ℝ) ≤ 31*(M:ℝ) := by positivity
  have cutCost := mul_le_mul_of_nonneg_left paidCut factor
  have cutCharge := mul_le_mul_of_nonneg_left paidFee factor
  have enough : 217*(M:ℝ)*K-32*(K:ℝ)^2 ≤ 248*(M:ℝ)*repaired := by
    nlinarith only [cropReal,cutCost,cutCharge]
  have branch : (0:ℝ) ≤ 3*(K:ℝ)-2*M := sub_nonneg.mpr (by exact_mod_cast lower)
  have below : (K:ℝ) ≤ M := by exact_mod_cast upper
  have margin : (0:ℝ) ≤ 587*(M:ℝ)-96*K := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have kept : 587*(M:ℝ)*M ≤ 1116*(repaired:ℝ)*M := by
    nlinarith only [enough,mul_nonneg branch margin]
  apply (Nat.mul_le_mul_right_iff positive).mp
  exact_mod_cast kept

private theorem sparse_width_fee_le_eighth {K D L : ℕ} (degree : 32 ≤ D) (length : 32 ≤ L) :
    8*(2*(K/D)+2*(K/L)) ≤ K := by
  have vCost : 32*(K/D) ≤ K := (Nat.mul_le_mul_right _ degree).trans
    (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self K D)
  have iCost : 32*(K/L) ≤ K := (Nat.mul_le_mul_right _ length).trans
    (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self K L)
  omega

/-- At half cutoff five the exact original-average caps hold when the
common-vertex-pair count E is at most the incidence mass M. The cleaned
witness fits both budgets and retains at least M/40. -/
theorem regularization_list_frozen_half_five_of_overlap_le_mass {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (overlap : commonVertexPairCount paths ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), (∀ i, (rows i).Nodup) ∧
      HalfBridgeFree (Before rows) 5 ∧ M ≤ 40*(∑ i, (rows i).length) ∧
      (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  change commonVertexPairCount paths ≤ M at overlap
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree.halfFree,by omega,upper,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  have vertexDense : 8*n ≤ M := by have fit := le_max_left n p; omega
  have pathDense : 8*p ≤ M := by have fit := le_max_right n p; omega
  have degreeWide : 32 ≤ D := (Nat.le_div_iff_mul_le hn).mpr (by omega)
  have lengthWide : 32 ≤ L := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  have Dpos : 0 < D := by omega
  have Lpos : 0 < L := by omega
  obtain ⟨kept,sub,paid,orders,safe,safeSub,safeFree,loss⟩ :=
    half_five_width_packing_after_sparse_overlap paths simple free Dpos Lpos
  let K := ∑ i, (kept i).length
  change 3*M ≤ 3*K+commonVertexPairCount paths at paid
  have enoughK : 2*M ≤ 3*K := by omega
  have upperK : K ≤ M := sum_le_sum (fun i _ => (sub i).length_le)
  let fee := 2*(K/D)+2*(K/L)
  have lossBudget : K ≤ (∑ j, (safe j).length)+fee := by
    simpa only [K,fee,Nat.add_assoc] using loss
  have feeBound : 8*fee ≤ K := sparse_width_fee_le_eighth degreeWide lengthWide
  let raw := orders.pieceRows D L
  let rawSets (j : orders.PathPiece L) := (raw j).toFinset
  have keptSimple (i : Fin p) := (sub i).nodup (simple i)
  have rawSimple (j : orders.PathPiece L) : (raw j).Nodup := orders.pieceRows_simple (keptSimple j.fst)
  have safeSimple (j : orders.PathPiece L) := (safeSub j).nodup (rawSimple j)
  have rawMass : (∑ j, (raw j).length) = K := orders.pieceRows_mass D L keptSimple
  have rawSetMass : (∑ j, (rawSets j).card) = K :=
    (sum_congr rfl (fun j _ => List.toFinset_card_of_nodup (rawSimple j))).trans rawMass
  have vRoom : 31*M ≤ 8*(D*n) := by
    have rounded : 4*M < D*n+n := four_average_width_product hn
    omega
  have iRoom : 31*M ≤ 8*(L*p) := by
    have rounded : 4*M < L*p+p := four_average_width_product hp
    omega
  obtain ⟨fullV,fullI,vFilled,vRemainder,iFilled,iRemainder⟩ :=
    orders.pieceRows_full_block_profiles Dpos Lpos keptSimple
  have iFilledSet (j : orders.PathPiece L) (full : j ∈ fullI) : L ≤ (rawSets j).card := by
    rw [show (rawSets j).card = (raw j).length from List.toFinset_card_of_nodup (rawSimple j)]
    exact (iFilled j full).ge
  have leftRoom : (∑ j, (rawSets j).card) ≤ D*n := by rw [rawSetMass]; omega
  have rightRoom : (∑ j, (rawSets j).card) ≤ L*p := by rw [rawSetMass]; omega
  have verticesRest : ((univ : Finset (orders.VertexCopy D)) \ fullV).card ≤ n := by
    have exactCount : ((univ : Finset (orders.VertexCopy D)) \ fullV).card = n :=
      vRemainder.trans (Fintype.card_fin n)
    omega
  have rowsRest : ((univ : Finset (orders.PathPiece L)) \ fullI).card ≤ p := by
    have exactCount : ((univ : Finset (orders.PathPiece L)) \ fullI).card = p :=
      iRemainder.trans (Fintype.card_fin p)
    omega
  obtain ⟨A,B,lostV,lostI,vFit,qFit,cropped,vLoss,iLoss⟩ := trim_width_supports rawSets fullV fullI Dpos Lpos
    (fun x full => (vFilled x full).ge) verticesRest iFilledSet rowsRest leftRoom rightRoom
  rw [rawSetMass] at cropped vLoss iLoss
  have recover : (∑ j ∈ B, (rawSets j ∩ A).card) ≤ (∑ j ∈ B, ((safe j).toFinset ∩ A).card)+fee :=
    restriction_loss_le_global raw safe rawSimple safeSub A B (by rw [rawMass]; exact lossBudget)
  have retained := half_five_sparse_crop_mass (hn.trans_le dense) enoughK upperK cropped recover feeBound
    vRoom iRoom vLoss iLoss
  let clean := restrictListPaths safe A B
  have cleanSimple (j : B) : (clean j).Nodup := restrictListPath_nodup (safeSimple j.val) A
  have cleanFree : HalfBridgeFree (Before clean) 5 := restrictListPaths_halfFree safeSimple safeFree A B
  have cleanMass : (∑ j, (clean j).length) = ∑ j ∈ B, ((safe j).toFinset ∩ A).card := by
    rw [← Finset.sum_attach B (fun j => ((safe j).toFinset ∩ A).card)]
    exact sum_congr rfl fun j _ => restrictListPath_length (safeSimple j.val) A
  have safeUpper : (∑ j, (safe j).length) ≤ M := calc
    _ ≤ ∑ j, (raw j).length := sum_le_sum (fun j _ => (safeSub j).length_le)
    _ = K := rawMass
    _ ≤ M := upperK
  have massUpper : (∑ j, (clean j).length) ≤ M := by
    rw [cleanMass]
    calc
      _ ≤ ∑ j ∈ B, (safe j).length := sum_le_sum (fun j _ => (card_le_card inter_subset_left).trans (List.toFinset_card_le _))
      _ ≤ ∑ j, (safe j).length := sum_le_sum_of_subset (subset_univ _)
      _ ≤ M := safeUpper
  obtain ⟨lengthCap,degreeCap⟩ := orders.pieceRows_caps Dpos Lpos keptSimple
  have finalLengths (j : B) : (clean j).length ≤ L := calc
    _ = ((safe j.val).toFinset ∩ A).card := restrictListPath_length (safeSimple j.val) A
    _ ≤ (safe j.val).length := (card_le_card inter_subset_left).trans (List.toFinset_card_le _)
    _ ≤ (raw j.val).length := (safeSub j.val).length_le
    _ ≤ L := lengthCap _
  have safeDegree (x : orders.VertexCopy D) : (occurrences (fun j => (safe j).toFinset) x).card ≤ D := by
    apply le_trans (card_le_card ?_) (degreeCap x)
    intro j on
    have contained := (mem_occurrences (marks := fun j => (safe j).toFinset)).mp on
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((safeSub j).subset (List.mem_toFinset.mp contained)))
  have finalDegrees (x : A) : (occurrences (fun j => (clean j).toFinset) x).card ≤ D := by
    have same : (fun j => (clean j).toFinset) = rectanglePaths (fun j => (safe j).toFinset) A B :=
      funext (restrictListPaths_toFinset safe A B)
    rw [same]
    exact (rectanglePaths_degree_le _ A B x).trans (safeDegree x.val)
  refine regularization_list_frozen_after_caps_with_ratios_of_mass (half := true) (k := 5) (retention := 40)
    (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1) clean cleanSimple cleanFree hn hp dense long
    (by decide) (by decide) (by decide) (by decide) ?_ ?_ finalLengths finalDegrees massUpper ?_
  · simpa only [one_mul,Fintype.card_coe] using vFit
  · simpa only [one_mul,Fintype.card_coe] using qFit
  · simp only [one_mul,cleanMass]
    omega

/-- The same overlap threshold gives distinct nonempty output on
literal input. Both original budgets and all four frozen caps remain. -/
theorem regularization_literal_frozen_half_five_of_overlap_le_mass {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (overlap : commonVertexPairCount paths ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v), Function.Injective rows ∧
      (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 40*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,rowsFree,retain,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by decide) hn hp dense low
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(rowsFree 5).halfFree,by omega,upper,caps⟩
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_of_ne_nil (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,caps⟩ :=
    regularization_list_frozen_half_five_of_overlap_le_mass paths (fun i => (valid i).2) free hn hp dense long overlap
  have mean : 4*p < M := by have fit := le_max_right n p; omega
  obtain ⟨oneToOne,nonempty⟩ := frozen_length_distinct_of_large_mean rowsSimple rowsFree (by decide) hp mean caps
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,rowsSimple i⟩,rowsFree,retain,upper,caps⟩

end OnlineReachabilityPreservers
