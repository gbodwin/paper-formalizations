import OnlineReachabilityPreservers.Regularization

/-! Exact vertex and path budgets and both degree caps for common-order systems. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem trim_weights {A : Type*} [DecidableEq A] (s : Finset A) (weight : A → ℕ) {n : ℕ}
    (size : n ≤ s.card) :
    ∃ t ⊆ s, t.card = n ∧ n*(∑ j ∈ s, weight j) ≤ s.card*(∑ j ∈ t, weight j) := by
  classical
  induction s using Finset.strongInduction generalizing n with
  | H s ih =>
    by_cases zero : n=0
    · exact ⟨∅,empty_subset _,by simp [zero]⟩
    by_cases same : n=s.card
    · exact ⟨s,Subset.rfl,same.symm,by rw [same]⟩
    have n0 : 0 < n := Nat.pos_of_ne_zero zero
    have s0 : 0 < s.card := n0.trans_le size
    obtain ⟨a,ha,least⟩ := exists_min_image s weight (card_pos.mp s0)
    let r := s.erase a
    have sizeEq : r.card+1 = s.card := card_erase_add_one ha
    have nr : n ≤ r.card := by omega
    have r0 : 0 < r.card := n0.trans_le nr
    obtain ⟨t,sub,eq,good⟩ := ih r (erase_ssubset ha) nr
    let M := ∑ j ∈ s, weight j
    let R := ∑ j ∈ r, weight j
    let T := ∑ j ∈ t, weight j
    have mass : R+weight a=M := sum_erase_add _ _ ha
    have leastSum : s.card*weight a ≤ M := by
      calc
        _ = ∑ _x ∈ s, weight a := by simp
        _ ≤ _ := sum_le_sum (fun x hx => least x hx)
    have low : r.card*weight a ≤ R := by
      have h : r.card*weight a+weight a ≤ R+weight a := by
        calc
          _ = (r.card+1)*weight a := by rw [Nat.add_mul,Nat.one_mul]
          _ = s.card*weight a := by rw [sizeEq]
          _ ≤ M := leastSum
          _ = _ := mass.symm
      omega
    have mean : r.card*M ≤ s.card*R := by
      calc
        _ = r.card*R+r.card*weight a := by rw [← mass,Nat.mul_add]
        _ ≤ r.card*R+R := Nat.add_le_add_left low _
        _ = _ := by rw [← sizeEq,Nat.add_mul,Nat.one_mul]
    refine ⟨t,sub.trans (erase_subset _ _),eq, Nat.le_of_mul_le_mul_right ?_ r0⟩
    change n*R ≤ r.card*T at good
    change (n*M)*r.card ≤ (s.card*T)*r.card
    calc
      _ = n*(r.card*M) := by ring
      _ ≤ n*(s.card*R) := Nat.mul_le_mul_left n mean
      _ = s.card*(n*R) := by ring
      _ ≤ s.card*(r.card*T) := Nat.mul_le_mul_left s.card good
      _ = _ := by ring

private theorem trim_weights_three_fourths {A : Type*} [DecidableEq A] (s : Finset A)
    (weight : A → ℕ) (n : ℕ) (expanded : 3*s.card ≤ 4*n) :
    ∃ t ⊆ s, t.card ≤ n ∧ 3*(∑ j ∈ s, weight j) ≤ 4*(∑ j ∈ t, weight j) := by
  by_cases keep : s.card ≤ n
  · refine ⟨s,Subset.rfl,keep,?_⟩
    omega
  have h : n ≤ s.card := le_of_not_ge keep
  obtain ⟨t,sub,eq,weight_bound⟩ := trim_weights s weight h
  have s0 : 0 < s.card := (Nat.zero_le n).trans_lt (Nat.lt_of_not_ge keep)
  refine ⟨t,sub,eq.le,Nat.le_of_mul_le_mul_right ?_ s0⟩
  let M := ∑ j ∈ s, weight j
  let T := ∑ j ∈ t, weight j
  change (3*M)*s.card ≤ (4*T)*s.card
  calc
    _ = (3*s.card)*M := by ring
    _ ≤ (4*n)*M := Nat.mul_le_mul_right M expanded
    _ = 4*(n*M) := by ring
    _ ≤ 4*(s.card*T) := Nat.mul_le_mul_left 4 weight_bound
    _ = _ := by ring

section Rectangle

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

private def rectangleMass (paths : I → Finset V) (A : Finset V) (B : Finset I) : ℕ :=
  ∑ i ∈ B, (paths i ∩ A).card

private def rectangularDegree (paths : I → Finset V) (B : Finset I) (v : V) : ℕ :=
  (B.filter fun i => v ∈ paths i).card

omit [DecidableEq I] in
private theorem rectangleMass_swap (paths : I → Finset V) (A : Finset V) (B : Finset I) :
    rectangleMass paths A B = ∑ v ∈ A, rectangularDegree paths B v := by
  have inner (i : I) : (paths i ∩ A).card = ∑ v ∈ A, if v ∈ paths i then 1 else 0 := by
    rw [← sum_filter]
    simp [filter_mem_eq_inter,inter_comm]
  have outer (v : V) :
      (∑ i ∈ B, if v ∈ paths i then 1 else 0) = rectangularDegree paths B v := by
    rw [← sum_filter]
    simp [rectangularDegree]
  unfold rectangleMass
  simp only [inner,sum_comm (s := B) (t := A),outer]

private theorem rectangle_trim (paths : I → Finset V) (A : Finset V) (B : Finset I) {n p : ℕ}
    (aLarge : 3*A.card ≤ 4*n) (bLarge : 3*B.card ≤ 4*p) :
    ∃ C ⊆ A, ∃ D ⊆ B, C.card ≤ n ∧ D.card ≤ p ∧
      9*rectangleMass paths A B ≤ 16*rectangleMass paths C D := by
  obtain ⟨C,hC,cSize,cMass⟩ := trim_weights_three_fourths A (rectangularDegree paths B) n aLarge
  obtain ⟨D,hD,dSize,dMass⟩ := trim_weights_three_fourths B (fun i => (paths i ∩ C).card) p bLarge
  rw [← rectangleMass_swap,← rectangleMass_swap] at cMass
  change 3*rectangleMass paths C B ≤ 4*rectangleMass paths C D at dMass
  exact ⟨C,hC,D,hD,cSize,dSize,by omega⟩

private theorem rectangle_prune (paths : I → Finset V) (A : Finset V) (B : Finset I)
    {d l : ℝ} (d0 : 0 ≤ d) (l0 : 0 ≤ l) :
    ∃ C ⊆ A, ∃ D ⊆ B,
      (rectangleMass paths A B:ℝ)-d*A.card-l*B.card ≤ rectangleMass paths C D ∧
      (∀ a ∈ C, d ≤ (rectangularDegree paths D a:ℝ)) ∧
      (∀ i ∈ D, l ≤ ((paths i ∩ C).card:ℝ)) := by
  classical
  let domain := A.powerset ×ˢ B.powerset
  let val (R : Finset V × Finset I) :=
    (rectangleMass paths R.1 R.2:ℝ)-d*R.1.card-l*R.2.card
  have included : (A,B) ∈ domain :=
    mem_product.mpr ⟨mem_powerset.mpr Subset.rfl,mem_powerset.mpr Subset.rfl⟩
  obtain ⟨⟨C,D⟩, mem, largest⟩ := exists_max_image domain val ⟨(A,B),included⟩
  obtain ⟨hC,hD⟩ := mem_product.mp mem
  have Csub : C ⊆ A := mem_powerset.mp hC
  have Dsub : D ⊆ B := mem_powerset.mp hD
  have low := largest (A,B) included
  change (rectangleMass paths A B:ℝ)-d*A.card-l*B.card ≤
    (rectangleMass paths C D:ℝ)-d*C.card-l*D.card at low
  refine ⟨C,Csub,D,Dsub,?_,?_,?_⟩
  · linarith only [low,mul_nonneg d0 (show (0:ℝ) ≤ C.card by positivity),
      mul_nonneg l0 (show (0:ℝ) ≤ D.card by positivity)]
  · intro a ha
    have left : (C.erase a,D) ∈ domain :=
      mem_product.mpr ⟨mem_powerset.mpr ((erase_subset _ _).trans Csub),hD⟩
    have h := largest (C.erase a,D) left
    have mc : (rectangleMass paths (C.erase a) D:ℝ)+(rectangularDegree paths D a:ℝ) =
        rectangleMass paths C D := by
      exact_mod_cast (show rectangleMass paths (C.erase a) D+rectangularDegree paths D a =
        rectangleMass paths C D by rw [rectangleMass_swap,rectangleMass_swap]; exact sum_erase_add _ _ ha)
    have cc : ((C.erase a).card:ℝ)+1 = C.card := by exact_mod_cast card_erase_add_one ha
    change (rectangleMass paths (C.erase a) D:ℝ)-d*(C.erase a).card-l*D.card ≤
      (rectangleMass paths C D:ℝ)-d*C.card-l*D.card at h
    rw [← cc,mul_add,mul_one] at h
    linarith only [h,mc]
  · intro i hi
    have right : (C,D.erase i) ∈ domain :=
      mem_product.mpr ⟨hC,mem_powerset.mpr ((erase_subset _ _).trans Dsub)⟩
    have h := largest (C,D.erase i) right
    have mc : (rectangleMass paths C (D.erase i):ℝ)+((paths i ∩ C).card:ℝ) =
        rectangleMass paths C D := by
      exact_mod_cast (show rectangleMass paths C (D.erase i)+(paths i ∩ C).card =
        rectangleMass paths C D from sum_erase_add _ _ hi)
    have cc : ((D.erase i).card:ℝ)+1 = D.card := by exact_mod_cast card_erase_add_one hi
    change (rectangleMass paths C (D.erase i):ℝ)-d*C.card-l*(D.erase i).card ≤
      (rectangleMass paths C D:ℝ)-d*C.card-l*D.card at h
    rw [← cc,mul_add,mul_one] at h
    linarith only [h,mc]

end Rectangle

section Ordered

variable {V I : Type*} [LinearOrder V] [LinearOrder I]

/-- The subsystem supported on the given vertices and paths. -/
def rectanglePaths (paths : I → Finset V) (A : Finset V) (B : Finset I) (i : ↥B) : Finset ↥A :=
  A.attach.filter fun v => v.1 ∈ paths i.1

omit [LinearOrder I] in
private theorem rectanglePath_card (paths : I → Finset V) (A : Finset V) (B : Finset I) (i : ↥B) :
    (rectanglePaths paths A B i).card = (paths i.1 ∩ A).card := by
  let R := rectanglePaths paths A B i
  have image : R.image Subtype.val = paths i.1 ∩ A := by
    ext v
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      exact mem_inter.mpr ⟨(mem_filter.mp ha).2,a.2⟩
    · intro h
      obtain ⟨path,ha⟩ := mem_inter.mp h
      exact mem_image.mpr ⟨⟨v,ha⟩,mem_filter.mpr ⟨mem_attach _ _,path⟩,rfl⟩
  change R.card = _
  rw [← card_image_of_injective _ Subtype.val_injective,image]

private theorem rectanglePath_degree (paths : I → Finset V) (A : Finset V) (B : Finset I) (v : ↥A) :
    (occurrences (rectanglePaths paths A B) v).card = rectangularDegree paths B v.1 := by
  let Q := occurrences (rectanglePaths paths A B) v
  have image : Q.image Subtype.val = B.filter (fun i => v.1 ∈ paths i) := by
    ext i
    constructor
    · intro h
      obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      have hv : v ∈ rectanglePaths paths A B j :=
        (mem_occurrences (marks := rectanglePaths paths A B)).mp hj
      exact mem_filter.mpr ⟨j.2,(mem_filter.mp hv).2⟩
    · intro h
      obtain ⟨hB,path⟩ := mem_filter.mp h
      have hv : v ∈ rectanglePaths paths A B ⟨i,hB⟩ :=
        mem_filter.mpr ⟨mem_attach _ _,path⟩
      exact mem_image.mpr ⟨⟨i,hB⟩,(mem_occurrences (marks := rectanglePaths paths A B)).mpr hv,rfl⟩
  change Q.card = _
  rw [← card_image_of_injective _ Subtype.val_injective,image]
  rfl

omit [LinearOrder I] in
private theorem rectanglePath_mass (paths : I → Finset V) (A : Finset V) (B : Finset I) :
    (∑ i : ↥B, (rectanglePaths paths A B i).card) = rectangleMass paths A B := by
  simp only [rectanglePath_card]
  exact (Finset.sum_subtype B (fun _ => Iff.rfl) (fun i => (paths i ∩ A).card)).symm

private def rectangleBridge (paths : I → Finset V) (A : Finset V) (B : Finset I) {k : ℕ}
    (b : Bridge (PathBefore (rectanglePaths paths A B)) k) : Bridge (PathBefore paths) k := by
  have before {i : ↥B} {u v : ↥A} (h : PathBefore (rectanglePaths paths A B) i u v) :
      PathBefore paths i.1 u.1 v.1 :=
    ⟨(mem_filter.mp h.1).2,(mem_filter.mp h.2.1).2,h.2.2⟩
  exact orderedBridge (fun i => (b.vertex i).1) (fun i => (b.arc i).1) b.river.1
    (fun _ _ eq => b.distinctArcs (Subtype.ext eq))
    (fun i eq => b.river_ne_arc i (Subtype.ext eq)) (before b.riverStep) (fun i => before (b.arcStep i))

private theorem rectangleHalfFree {paths : I → Finset V} (A : Finset V) (B : Finset I)
    (free : HalfBridgeFree (PathBefore paths) 4) :
    HalfBridgeFree (PathBefore (rectanglePaths paths A B)) 4 := by
  intro k size b earlier
  exact free size (rectangleBridge paths A B b) earlier

omit [LinearOrder I] in
private theorem rectangleFullFree {paths : I → Finset V} (A : Finset V) (B : Finset I)
    (free : BridgeFree (PathBefore paths) 4) :
    BridgeFree (PathBefore (rectanglePaths paths A B)) 4 := by
  intro k size
  exact ⟨fun b => (free size).false (rectangleBridge paths A B b)⟩

variable [Fintype V] [Fintype I]

omit [LinearOrder V] [LinearOrder I] [Fintype V] in
private theorem blockIndex_card_precise (sets : I → Finset V) {w : ℕ} (hw : 0 < w) :
    Fintype.card (BlockIndex sets w) ≤ Fintype.card I+(∑ i, (sets i).card)/w := by
  rw [Fintype.card_lex,Fintype.card_sigma]
  have count (i : I) : Fintype.card (Fin (blockCount (sets i) w)) =
      (sets i).card/w+1 := Fintype.card_fin _
  simp only [count,sum_add_distrib,sum_const,card_univ,smul_eq_mul,mul_one]
  have b : (∑ i, (sets i).card/w) ≤ (∑ i, (sets i).card)/w := by
    apply (Nat.le_div_iff_mul_le hw).mpr
    rw [sum_mul]
    exact sum_le_sum (fun i _ => Nat.div_mul_le_self (sets i).card w)
  omega

private theorem four_average_width {M q : ℕ} (hq : 0 < q) (dense : q ≤ M) :
    let w := (4*M)/q
    0 < w ∧ 3*(M/w) ≤ q ∧ (w:ℝ) ≤ 4*(M:ℝ)/(q:ℝ) := by
  let w := (4*M)/q
  have hw : 0 < w := Nat.div_pos (by omega) hq
  have large := Nat.lt_mul_div_succ (4*M) hq
  change 4*M < q*(w+1) at large
  rw [Nat.mul_succ] at large
  have hM : 3*M ≤ q*w := by omega
  have trim : 3*(M/w) ≤ q := by
    apply Nat.le_of_mul_le_mul_right _ hw
    calc
      _ = 3*((M/w)*w) := by ring
      _ ≤ 3*M := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ ≤ _ := hM
  have cap : (w:ℝ) ≤ 4*(M:ℝ)/(q:ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hq)).mpr
    exact_mod_cast Nat.div_mul_le_self (4*M) q
  exact ⟨hw,trim,cap⟩

set_option maxHeartbeats 1000000 in
/-- With a common vertex order and incidence mass at least both original counts,
splitting, restriction, and pruning meet both budgets and all four average caps.
The surviving mass is at least a sixteenth of the original mass. -/
theorem regularization_balanced_caps (paths : I → Finset V) (hn : 0 < Fintype.card V)
    (hp : 0 < Fintype.card I) (dense : Fintype.card V ≤ ∑ i, (paths i).card)
    (long : Fintype.card I ≤ ∑ i, (paths i).card) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).card
    let d := (4*M)/n
    let l := (4*M)/p
    let splitV := splitVertices paths d
    let Z := splitPaths splitV l
    ∃ A : Finset (VertexBlockIndex paths d), ∃ B : Finset (BlockIndex splitV l),
      let clean := rectanglePaths Z A B
      A.card ≤ n ∧ B.card ≤ p ∧ M ≤ 16*(∑ i, (clean i).card) ∧
        (∀ v, (M:ℝ)/(4*(n:ℝ)) ≤ (occurrences clean v).card ∧
          ((occurrences clean v).card:ℝ) ≤ 4*(M:ℝ)/(n:ℝ)) ∧
        (∀ i, (M:ℝ)/(4*(p:ℝ)) ≤ (clean i).card ∧
          ((clean i).card:ℝ) ≤ 4*(M:ℝ)/(p:ℝ)) ∧
        (HalfBridgeFree (PathBefore paths) 4 → HalfBridgeFree (PathBefore clean) 4) ∧
        (BridgeFree (PathBefore paths) 4 → BridgeFree (PathBefore clean) 4) := by
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let d := (4*M)/n
  let l := (4*M)/p
  let s := splitVertices paths d
  let Z := splitPaths s l
  let A0 := (univ : Finset (VertexBlockIndex paths d))
  let B0 := (univ : Finset (BlockIndex s l))
  let d0 : ℝ := (M:ℝ)/(4*(n:ℝ))
  let l0 : ℝ := (M:ℝ)/(4*(p:ℝ))
  obtain ⟨hd,reduceD,dCap⟩ := four_average_width hn dense
  obtain ⟨hl,reduceL,lCap⟩ := four_average_width hp long
  have sMass : (∑ i, (s i).card) = M := by
    simp only [s,splitVertices_length,M]
  have ZMass : rectangleMass Z A0 B0 = M := by
    simp only [rectangleMass,A0,B0,inter_univ,Z]
    exact (splitPaths_size s l).trans sMass
  have vertices : 3*A0.card ≤ 4*n := by
    have h := blockIndex_card_precise (occurrences paths) hd
    rw [sum_occurrences] at h
    change A0.card ≤ n+M/d at h
    change 3*(M/d) ≤ n at reduceD
    omega
  have families : 3*B0.card ≤ 4*p := by
    have h := blockIndex_card_precise s hl
    rw [sMass] at h
    change B0.card ≤ p+M/l at h
    change 3*(M/l) ≤ p at reduceL
    omega
  obtain ⟨A1,_,B1,_,ac,bc,densePart⟩ := rectangle_trim Z A0 B0 vertices families
  have d0_nonneg : 0 ≤ d0 := div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have l0_nonneg : 0 ≤ l0 := div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  obtain ⟨A,as,B,bs,keep,minDegree,minLength⟩ := rectangle_prune Z A1 B1 d0_nonneg l0_nonneg
  let clean := rectanglePaths Z A B
  have loseDegree : d0*(A1.card:ℝ) ≤ (M:ℝ)/4 := by
    calc
      _ ≤ d0*(n:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ac) d0_nonneg
      _ = _ := by
        dsimp [d0]
        have h : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
        field_simp
  have loseLength : l0*(B1.card:ℝ) ≤ (M:ℝ)/4 := by
    calc
      _ ≤ l0*(p:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr bc) l0_nonneg
      _ = _ := by
        dsimp [l0]
        have h : (p:ℝ) ≠ 0 := (Nat.cast_pos.mpr hp).ne'
        field_simp
  have part : 9*(M:ℝ) ≤ 16*(rectangleMass Z A1 B1:ℝ) := by
    rw [ZMass] at densePart
    exact_mod_cast densePart
  have finalMass : M ≤ 16*(∑ i, (clean i).card) := by
    rw [rectanglePath_mass]
    have h : (M:ℝ) ≤ 16*(rectangleMass Z A B:ℝ) := by
      linarith only [part,keep,loseDegree,loseLength]
    exact_mod_cast h
  refine ⟨A,B,(card_le_card as).trans ac,(card_le_card bs).trans bc,finalMass,?_,?_,
    fun free => rectangleHalfFree A B (regularization_halfFree free d l),
    fun free => rectangleFullFree A B (regularization_free free d l)⟩
  · intro v
    change d0 ≤ ((occurrences clean v).card : ℝ) ∧
      ((occurrences clean v).card : ℝ) ≤ 4 * (M : ℝ) / (n : ℝ)
    rw [show (occurrences clean v).card = rectangularDegree Z B v.1 from
      rectanglePath_degree Z A B v]
    refine ⟨minDegree v.1 v.2,?_⟩
    have sub : B.filter (fun i => v.1 ∈ Z i) ⊆ occurrences Z v.1 :=
      fun _ h => mem_occurrences.mpr (mem_filter.mp h).2
    have cap := ((card_le_card sub).trans (splitPaths_degree s l v.1)).trans
      (splitVertices_degree paths hd v.1)
    exact (Nat.cast_le.mpr cap).trans dCap
  · intro i
    change l0 ≤ ((clean i).card : ℝ) ∧ ((clean i).card : ℝ) ≤ 4 * (M : ℝ) / (p : ℝ)
    rw [show (clean i).card = (Z i.1 ∩ A).card from rectanglePath_card Z A B i]
    refine ⟨minLength i.1 i.2,?_⟩
    have cap := (card_le_card (inter_subset_left : Z i.1 ∩ A ⊆ Z i.1)).trans
      (splitPaths_length s hl i.1)
    exact (Nat.cast_le.mpr cap).trans lCap

end Ordered

end OnlineReachabilityPreservers
