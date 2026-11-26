import OnlineReachabilityPreservers.FrozenOverlongPaths

/-! Frozen cleaning of a sufficiently massive length-capped subfamily. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem frozen_length_capped_retention {M K : ℝ} (positive : 0 < M) (lower : 8*M ≤ 15*K)
    (upper : K ≤ M) : M/104 ≤ K-K^2/(12*M)-M/2 := by
  rw [show K-K^2/(12*M)-M/2 = (12*M*K-K^2-6*M^2)/(12*M) from by
    field_simp [positive.ne']
    ring]
  apply (le_div_iff₀ (by positivity)).mpr
  have quadratic := mul_nonneg (show 0 ≤ K-8*M/15 by linarith) (show 0 ≤ 12*M-K-8*M/15 by linarith)
  nlinarith

/-- Row splitting is unnecessary for a length-capped subfamily carrying
at least eight fifteenths of the original mass. Vertex trimming and
peeling then give both budgets and all four frozen caps. -/
theorem regularization_list_frozen_of_length_capped_mass {I : Type*} [LinearOrder I] [Fintype I]
    {half : Bool} {k n p M : ℕ} (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (pathsCap : Fintype.card I ≤ p) (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (upper : (∑ i, (paths i).length) ≤ M) (lower : 8*M ≤ 15*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4*M/n
  let K := ∑ i, (paths i).length
  let copied := splitListVertices paths D
  obtain ⟨width,_,_⟩ := four_average_width hn dense
  have copiedSimple (i : I) : (copied i).Nodup := splitListVertices_simple paths D i (simple i)
  have steps {i : I} {x y : ListVertexBlockIndex paths D} (step : ListBefore copied i x y) :
      ListBefore paths i x.fst y.fst := splitListVertices_step (simple i) step
  have legal : localOrderAdmissible half k copied := by
    cases half
    · exact BridgeFree.split_list_vertices_any allowed (·.fst) (fun {_ _ _} => steps)
    · exact HalfBridgeFree.split_list_vertices_short allowed (size rfl) (·.fst) (fun {_ _ _} => steps)
  have copyLength (i : I) : (copied i).length = (paths i).length := splitListVertices_length paths D i
  have copiesAsSets : (fun i => (copied i).toFinset) = splitVertices (fun i => (paths i).toFinset) D :=
    funext (splitListVertices_toFinset paths D)
  have degreeCap (v : ListVertexBlockIndex paths D) : (occurrences (fun i => (copied i).toFinset) v).card ≤ D := by
    rw [copiesAsSets]
    exact splitVertices_degree _ width v
  have mass : (∑ i, (copied i).length) = K := sum_congr rfl (fun i _ => copyLength i)
  obtain ⟨filled,exactFilled,other⟩ := splitListVertices_full_block_profile paths width
  have remainders : (univ \ filled).card ≤ n := by rw [other,Fintype.card_fin]
  refine regularization_list_frozen_trim_vertices_quadratic copied copiedSimple legal hn hp dense long
    (retention := 104) (by decide) filled exactFilled remainders pathsCap
    (fun i => (copyLength i).trans_le (lengthCap i)) degreeCap (mass.trans_le upper) ?_
  rw [mass]
  have massPos : (0:ℝ) < M := by exact_mod_cast hn.trans_le dense
  let l : ℝ := (M:ℝ)/(4*(p:ℝ))
  have total : l*(p:ℝ) = (M:ℝ)/4 := by
    have p0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    dsimp [l]
    field_simp [p0]
  have pathLoss : l*(Fintype.card I:ℝ) ≤ (M:ℝ)/4 :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr pathsCap) (by positivity)).trans_eq total
  have retain := frozen_length_capped_retention (M := (M:ℝ)) (K := (K:ℝ)) massPos
    (by exact_mod_cast lower) (by exact_mod_cast upper)
  change (M:ℝ)/104 ≤ (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-l*(Fintype.card I:ℝ)
  linarith

/-- In particular, it suffices that at most seven fifteenths of the
input mass lies on rows exceeding the original upper length cap. -/
theorem regularization_list_frozen_of_small_overlong_mass {half : Bool} {k n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : let M := ∑ i, (paths i).length; 15*listMassAboveWidth paths (4*M/p) ≤ 7*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let short := univ.filter (fun i => (paths i).length ≤ L)
  let chosen (i : short) := paths i.val
  let K := ∑ i, (chosen i).length
  have cap : Fintype.card short ≤ p := by
    simpa only [Fintype.card_coe,card_univ,Fintype.card_fin] using card_le_card (subset_univ short)
  have oldMass : K+listMassAboveWidth paths L = M := by
    change (∑ i : short, (paths i.val).length)+listMassAboveWidth paths L = M
    have extract : (∑ i : short, (paths i.val).length) = ∑ i ∈ short, (paths i).length :=
      sum_attach short (fun i => (paths i).length)
    rw [extract]
    unfold short listMassAboveWidth M
    simpa only [not_le] using sum_filter_add_sum_filter_not (univ : Finset (Fin p))
      (fun i => (paths i).length ≤ L) (fun i => (paths i).length)
  have admissible : localOrderAdmissible half k chosen := by
    cases half
    · change BridgeFree (ListBefore paths) k at allowed
      change BridgeFree (ListBefore chosen) k
      intro t former
      exact ⟨fun b => (allowed former).false (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step))⟩
    · change HalfBridgeFree (ListBefore paths) k at allowed
      change HalfBridgeFree (ListBefore chosen) k
      intro t former b earlier
      exact allowed former (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step)) earlier
  exact regularization_list_frozen_of_length_capped_mass chosen (fun i => simple i.val) admissible size hn hp dense long
    cap (fun i => (mem_filter.mp i.property).2) (by omega) (by change 15*listMassAboveWidth paths L ≤ 7*M at small; omega)

end OnlineReachabilityPreservers
