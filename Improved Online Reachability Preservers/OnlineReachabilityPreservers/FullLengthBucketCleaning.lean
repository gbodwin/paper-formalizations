import OnlineReachabilityPreservers.OutputAverageDistinctCleaning
import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Logarithmic-loss full cleaning through the original finite cutoff. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "ListBefore" => SourceAudit.BeforeIn

/-- Clean a dense group of similarly long rows by splitting only vertices.
The maximum allowed length is at most three halves of the mean length.
Filled degree blocks are kept first, and the remaining vertex budget goes
to the heaviest remainders. -/
theorem regularization_list_output_average_full_of_length_bucket {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] {k L : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) k) (hn : 0 < Fintype.card V)
    (dense : 4*Fintype.card V ≤ ∑ i, (paths i).length)
    (maxLength : ∀ i, (paths i).length ≤ L)
    (lengthCharge : 2*(L*Fintype.card I) ≤ 3*(∑ i, (paths i).length)) :
    let K := ∑ i, (paths i).length
    ∃ n' ≤ Fintype.card V, ∃ p' ≤ Fintype.card I, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      K ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ K ∧ listOutputAverageCaps clean := by
  let n := Fintype.card V
  let K := ∑ i, (paths i).length
  let D := (K+n-1)/n
  have Kpos : 0 < K := by change 4*n ≤ K at dense; omega
  have capacity : K ≤ D*n := by
    have floor := Nat.lt_mul_div_succ (K+n-1) hn
    change K+n-1 < n*(D+1) at floor
    rw [Nat.mul_succ,Nat.mul_comm n D] at floor
    omega
  have width : 0 < D := Nat.pos_of_ne_zero fun zero => by
    rw [zero,Nat.zero_mul] at capacity
    omega
  have degreeCharge : 4*(D*n) ≤ 5*K := by
    have floor : D*n ≤ K+n-1 := Nat.div_mul_le_self _ _
    change 4*n ≤ K at dense
    omega
  let copies := splitListVertices paths D
  let Z (i : I) := (copies i).toFinset
  have copiesSimple (i : I) : (copies i).Nodup := splitListVertices_simple paths D i (simple i)
  have copiesFree : BridgeFree (ListBefore copies) k := free.split_list_vertices_any (·.fst)
    (fun {i _ _} step => splitListVertices_step (simple i) step)
  have counted : (∑ i, (Z i).card) = K := by
    exact sum_congr rfl (fun i _ => (List.toFinset_card_of_nodup (copiesSimple i)).trans
      (splitListVertices_length paths D i))
  have degree (v : ListVertexBlockIndex paths D) : (occurrences Z v).card ≤ D := by
    simpa only [Z,copies,splitListVertices_toFinset] using
      splitVertices_degree (fun i => (paths i).toFinset) width v
  obtain ⟨filled,full,rest⟩ := splitListVertices_full_block_profile paths width
  obtain ⟨A,aFits,loss,trim,crop⟩ := trim_full_vertex_blocks_quadratic Z filled width full rest.le
    (by rw [counted]; exact capacity)
  rw [counted] at trim crop
  have lossBound : 4*loss ≤ K := by
    apply Nat.le_of_mul_le_mul_left (c := K) _ Kpos
    calc
      _ ≤ (D*n)*(4*loss) := Nat.mul_le_mul_right _ capacity
      _ = 4*(D*n)*loss := by ring
      _ ≤ K^2 := trim
      _ = K*K := pow_two _
  let d : ℝ := (D:ℝ)/4
  let l : ℝ := (L:ℝ)/4
  have d0 : 0 ≤ d := by dsimp [d]; positivity
  have l0 : 0 ≤ l := by dsimp [l]; positivity
  obtain ⟨C,cSub,B,bSub,retained,minD,minL⟩ := rectanglePaths_prune Z A (univ : Finset I) d0 l0
  have vertexCost : d*(A.card:ℝ) ≤ 5*(K:ℝ)/16 := by
    have countR : (A.card:ℝ) ≤ n := by exact_mod_cast aFits
    have degreeR : 4*((D:ℝ)*n) ≤ 5*(K:ℝ) := by exact_mod_cast degreeCharge
    have leWidth := mul_le_mul_of_nonneg_left countR d0
    dsimp [d] at leWidth ⊢
    linarith only [degreeR,leWidth]
  have rowCost : l*Fintype.card I ≤ 3*(K:ℝ)/8 := by
    have lengths : 2*((L:ℝ)*Fintype.card I) ≤ 3*(K:ℝ) := by exact_mod_cast lengthCharge
    dsimp [l]
    linarith only [lengths]
  have lostR : 4*(loss:ℝ) ≤ K := by exact_mod_cast lossBound
  have cropR : ((∑ i : (univ : Finset I), (rectanglePaths Z A univ i).card : ℕ) : ℝ)+(loss:ℝ) = K := by
    exact_mod_cast crop
  rw [card_univ] at retained
  have kept : K ≤ 16*(∑ i : B, (rectanglePaths Z C B i).card) := by
    exact_mod_cast (show (K:ℝ) ≤ 16*((∑ i : B, (rectanglePaths Z C B i).card : ℕ):ℝ) by
      linarith only [vertexCost,rowCost,lostR,cropR,retained])
  let restricted := restrictListPaths copies C B
  have restrictedSimple (i : B) : (restricted i).Nodup := restrictListPath_nodup (copiesSimple i.val) C
  have restrictedFree := restrictListPaths_fullFree copiesSimple copiesFree C B
  have marks : (fun i => (restricted i).toFinset) = rectanglePaths Z C B :=
    funext (restrictListPaths_toFinset copies C B)
  have mass : (∑ i : B, (restricted i).length) = ∑ i : B, (rectanglePaths Z C B i).card :=
    sum_congr rfl (fun i _ => (List.toFinset_card_of_nodup (restrictedSimple i)).symm.trans
      (congrArg Finset.card (congrFun marks i)))
  have caps : listOutputAverageCaps restricted := by
    apply listOutputAverageCaps_of_widths restricted restrictedSimple D L
    · intro v
      rw [marks]
      exact ⟨minD v,Nat.cast_le.mpr ((rectanglePaths_degree_le Z C B v).trans (degree v.val))⟩
    · intro i
      have size : (restricted i).length = (rectanglePaths Z C B i).card := by
        rw [← List.toFinset_card_of_nodup (restrictedSimple i),congrFun marks i]
      have upper : (restricted i).length ≤ L := by
        rw [show (restricted i).length = ((copies i.val).toFinset ∩ C).card from
          restrictListPath_length (copiesSimple i.val) C]
        exact (card_le_card inter_subset_left).trans ((List.toFinset_card_le _).trans
          ((splitListVertices_length paths D i.val).le.trans (maxLength i.val)))
      exact ⟨by rw [size]; exact minL i,Nat.cast_le.mpr upper⟩
  obtain ⟨clean,cleanSimple,cleanFree,cleanMass,cleanCaps⟩ :=
    listOutputAverageCaps_relabel restricted restrictedSimple false restrictedFree caps
  refine ⟨Fintype.card C,?_,Fintype.card B,?_,clean,cleanSimple,cleanFree,?_,?_,cleanCaps⟩
  · simpa only [Fintype.card_coe] using (card_le_card cSub).trans aFits
  · simpa only [Fintype.card_coe] using card_le_univ B
  · rwa [cleanMass,mass]
  · rw [cleanMass,mass]
    exact (rectanglePaths_mass_le Z C B).trans_eq counted

private theorem length_bucket_mass {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) :
    ∃ B : Finset (Fin p), ∃ L : ℕ,
      (∑ i, (paths i).length) ≤ (2*(Nat.log 2 n+1))*(∑ i : B, (paths i.val).length) ∧
      (∀ i : B, (paths i.val).length ≤ L) ∧ 2*(L*B.card) ≤ 3*(∑ i : B, (paths i.val).length) := by
  let size (i : Fin p) := (paths i).length
  let Label := Fin (Nat.log 2 n+1) × Bool
  let active := (univ : Finset (Fin p)).filter fun i => 0 < size i
  have sizeLe (i : Fin p) : size i ≤ n := by
    rw [show size i = (paths i).toFinset.card from (List.toFinset_card_of_nodup (simple i)).symm]
    simpa using card_le_univ (paths i).toFinset
  let label (i : Fin p) : Label :=
    (⟨Nat.log 2 (size i),Nat.lt_succ_of_le (Nat.log_mono_right (sizeLe i))⟩,
      decide (2*size i ≤ 3*2^(Nat.log 2 (size i))))
  let bucket (j : Label) := active.filter fun i => label i = j
  let weight (j : Label) := ∑ i ∈ bucket j, size i
  have allMass : (∑ i, size i) = ∑ j, weight j := by
    calc
      _ = ∑ i ∈ active, size i := by
        rw [show active = univ.filter (fun i => 0 < size i) from rfl,sum_filter]
        apply sum_congr rfl
        intro i _
        by_cases positive : 0 < size i
        · simp only [positive,ite_true]
        · have empty : size i = 0 := by omega
          rw [ite_eq_right positive,empty]
      _ = _ := (sum_fiberwise_of_maps_to (fun i (_ : i ∈ active) => mem_univ (label i)) size).symm
  have labelsNonempty : (univ : Finset Label).Nonempty := ⟨(⟨0,by omega⟩,false),mem_univ _⟩
  obtain ⟨j,_,maximal⟩ := exists_max_image univ weight labelsNonempty
  let L := if j.2 then 3*2^j.1.val/2 else 2*2^j.1.val
  have widths (i : bucket j) : size i.val ≤ L ∧ 2*L ≤ 3*size i.val := by
    have on := mem_filter.mp i.property
    have positive : 0 < size i.val := (mem_filter.mp on.1).2
    have level : Nat.log 2 (size i.val) = j.1.val := congrArg (fun c : Label => c.1.val) on.2
    have bit : decide (2*size i.val ≤ 3*2^(Nat.log 2 (size i.val))) = j.2 := congrArg Prod.snd on.2
    have near := Nat.pow_log_le_self 2 (Nat.ne_of_gt positive)
    have wide := Nat.lt_pow_succ_log_self (b := 2) (by decide) (size i.val)
    rw [level] at near
    rw [level,Nat.pow_succ] at wide
    by_cases below : 2*size i.val ≤ 3*2^(Nat.log 2 (size i.val))
    · have low : j.2 = true := by simpa only [below,decide_true,eq_comm] using bit
      rw [level] at below
      simp only [L,low,ite_true]
      omega
    · have high : j.2 = false := by simpa only [below,decide_false,eq_comm] using bit
      rw [level] at below
      simp only [L,high,Bool.false_eq_true,ite_false]
      omega
  have mass : (∑ i : bucket j, size i.val) = weight j := (bucket j).sum_coe_sort size
  have cardLabel : Fintype.card Label = 2*(Nat.log 2 n+1) := by simp [Label,Nat.mul_comm]
  refine ⟨bucket j,L,?_,fun i => (widths i).1,?_⟩
  · change (∑ i, size i) ≤ (2*(Nat.log 2 n+1))*(∑ i : bucket j, size i.val)
    rw [allMass,mass]
    calc
      _ ≤ ∑ _ : Label, weight j := sum_le_sum fun c _ => maximal c (mem_univ _)
      _ = _ := by simp only [sum_const,card_univ,cardLabel,nsmul_eq_mul,Nat.cast_id]
  · change 2*(L*(bucket j).card) ≤ 3*(∑ i : bucket j, size i.val)
    calc
      _ = ∑ _i : bucket j, 2*L := by
        rw [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id]
        ring
      _ ≤ ∑ i : bucket j, 3*size i.val := sum_le_sum fun i _ => (widths i).2
      _ = _ := (mul_sum _ _ _).symm

/-- At every full cutoff, keeping one bucket of comparable row lengths
and splitting only vertices gives factor-four caps at the output averages.
The loss is at most `32*(Nat.log 2 n+1)` of the original mass. -/
theorem regularization_list_output_average_full_logarithmic {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ (32*(Nat.log 2 n+1))*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  let count := 2*(Nat.log 2 n+1)
  obtain ⟨B,L,mass,maxLength,lengthCharge⟩ := length_bucket_mass paths simple
  let bucket (i : B) := paths i.val
  let K := ∑ i : B, (bucket i).length
  have bucketSimple (i : B) : (bucket i).Nodup := simple i.val
  have bucketFree : BridgeFree (ListBefore bucket) k := fun _ bound =>
    ⟨fun bridge => (free bound).false (bridge.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step))⟩
  have K_le_M : K ≤ M := by
    change (∑ i : B, (paths i.val).length) ≤ M
    calc
      _ = ∑ i ∈ B, (paths i).length := B.sum_coe_sort (fun i => (paths i).length)
      _ ≤ M := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have account : 16*count = 32*(Nat.log 2 n+1) := by dsimp [count]; ring
  change M ≤ count*K at mass
  by_cases enough : 4*n ≤ K
  · obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,keeps,within,caps⟩ :=
      regularization_list_output_average_full_of_length_bucket bucket bucketSimple bucketFree
        (by simpa only [Fintype.card_fin] using hn) (by simpa only [Fintype.card_fin] using enough)
        maxLength (by simpa only [Fintype.card_coe] using lengthCharge)
    have many : Fintype.card B ≤ p := by simpa using card_le_univ B
    refine ⟨v,by simpa only [Fintype.card_fin] using vFits,q,qFits.trans many,clean,cleanSimple,cleanFree,?_,
      within.trans K_le_M,caps⟩
    rw [← account,Nat.mul_comm 16 count,Nat.mul_assoc]
    exact mass.trans (Nat.mul_le_mul_left _ keeps)
  · let clean : Fin 1 → List (Fin n) := fun _ => List.finRange n
    have cleanSimple (i : Fin 1) : (clean i).Nodup := List.nodup_finRange _
    have cleanMass : (∑ i, (clean i).length) = n := by simp [clean]
    have caps : listOutputAverageCaps clean := by
      apply listOutputAverageCaps_of_widths clean cleanSimple 1 (n:ℝ)
      · intro v
        have degree : (occurrences (fun i => (clean i).toFinset) v).card = 1 := by simp [occurrences,clean]
        norm_num [degree]
      · intro i
        have nonneg : (0:ℝ) ≤ n := Nat.cast_nonneg _
        simp only [clean,List.length_finRange]
        exact ⟨by linarith,le_rfl⟩
    refine ⟨n,le_rfl,1,hp,clean,cleanSimple,fun _ _ => ⟨fun b => b.river_ne_arc 0 (Subsingleton.elim _ _)⟩,
      ?_, cleanMass.le.trans dense,caps⟩
    rw [cleanMass,← account,Nat.mul_comm 16 count,Nat.mul_assoc]
    exact mass.trans (Nat.mul_le_mul_left _ (by omega))

/-- At each full cutoff, the logarithmic bound also applies to the
unrestricted indexed maximum. -/
theorem localOrderExtremal_output_average_full_logarithmic (n p k : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (ListBefore paths) k ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (ListBefore other) k →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
        M ≤ (32*(Nat.log 2 n+1))*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,simple,free,best,dense,_⟩ := localOrderExtremal_isDense n p k false hn hp
  exact ⟨paths,simple,free,best,regularization_list_output_average_full_logarithmic paths simple free hn hp dense⟩

/-- The logarithmic mass bound also holds for distinct nonempty input
and output at every full cutoff of at least two. -/
theorem regularization_list_output_average_full_distinct_logarithmic {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (rows : ∀ i, paths i ≠ [] ∧ (paths i).Nodup) (free : BridgeFree (ListBefore paths) k)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ (576*(Nat.log 2 n+1))*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  obtain ⟨v,vFits,q,qFits,clean,unique,nonempty,simple,legal,mass,upper,caps⟩ :=
    regularization_list_output_average_distinct_of_indexed_with_retention (half := false)
      paths distinct (fun i => (rows i).1) (fun i => (rows i).2) free two hn hp dense
      (fun _ => regularization_list_output_average_full_logarithmic paths (fun i => (rows i).2) free hn hp dense)
  have scale : 18*(32*(Nat.log 2 n+1)) = 576*(Nat.log 2 n+1) := by ring
  rw [scale] at mass
  exact ⟨v,vFits,q,qFits,clean,unique,fun i => ⟨nonempty i,simple i⟩,legal,mass,upper,caps⟩

/-- Feasible exact literal budgets have the logarithmic-loss witness
at the unrestricted full maximum, with the original cutoff. -/
theorem localOrderDistinctExtremal_output_average_full_logarithmic {n p k : ℕ}
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ k)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (ListBefore paths) k) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (ListBefore paths) k ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (ListBefore other) k →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
        M ≤ (576*(Nat.log 2 n+1))*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,distinct,rows,free,best,dense,_⟩ := localOrderDistinctExtremal_isDense false hp feasible
  exact ⟨paths,distinct,rows,free,best,
    regularization_list_output_average_full_distinct_logarithmic paths distinct rows free two hn hp dense⟩

end OnlineReachabilityPreservers
