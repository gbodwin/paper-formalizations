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
/-- Retain a prescribed fraction of the weight within a smaller budget. -/
theorem trim_weights_ratio {A : Type*} [DecidableEq A] (s : Finset A)
    (weight : A → ℕ) {n a b : ℕ} (ratio : a ≤ b) (expanded : a*s.card ≤ b*n) :
    ∃ t ⊆ s, t.card ≤ n ∧ a*(∑ j ∈ s, weight j) ≤ b*(∑ j ∈ t, weight j) := by
  by_cases keep : s.card ≤ n
  · exact ⟨s,Subset.rfl,keep,Nat.mul_le_mul_right _ ratio⟩
  have h : n ≤ s.card := le_of_not_ge keep
  obtain ⟨t,sub,eq,weight_bound⟩ := trim_weights s weight h
  have s0 : 0 < s.card := (Nat.zero_le n).trans_lt (Nat.lt_of_not_ge keep)
  refine ⟨t,sub,eq.le,Nat.le_of_mul_le_mul_right ?_ s0⟩
  let M := ∑ j ∈ s, weight j
  let T := ∑ j ∈ t, weight j
  change (a*M)*s.card ≤ (b*T)*s.card
  calc
    _ = (a*s.card)*M := by ring
    _ ≤ (b*n)*M := Nat.mul_le_mul_right M expanded
    _ = b*(n*M) := by ring
    _ ≤ b*(s.card*T) := Nat.mul_le_mul_left b weight_bound
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

private theorem rectangle_trim_ratios (paths : I → Finset V) (A : Finset V) (B : Finset I) {n p a b c d : ℕ}
    (rowRatio : a ≤ b) (colRatio : c ≤ d)
    (aLarge : a*A.card ≤ b*n) (bLarge : c*B.card ≤ d*p) :
    ∃ C ⊆ A, ∃ D ⊆ B, C.card ≤ n ∧ D.card ≤ p ∧
      (a*c)*rectangleMass paths A B ≤ (b*d)*rectangleMass paths C D := by
  obtain ⟨C,hC,cSize,cMass⟩ := trim_weights_ratio A (rectangularDegree paths B) rowRatio aLarge
  obtain ⟨D,hD,dSize,dMass⟩ := trim_weights_ratio B (fun i => (paths i ∩ C).card) colRatio bLarge
  rw [← rectangleMass_swap,← rectangleMass_swap] at cMass
  change c*rectangleMass paths C B ≤ d*rectangleMass paths C D at dMass
  refine ⟨C,hC,D,hD,cSize,dSize,?_⟩
  calc
    _ = c*(a*rectangleMass paths A B) := by ring
    _ ≤ c*(b*rectangleMass paths C B) := Nat.mul_le_mul_left c cMass
    _ = b*(c*rectangleMass paths C B) := by ring
    _ ≤ b*(d*rectangleMass paths C D) := Nat.mul_le_mul_left b dMass
    _ = _ := by ring

private theorem rectangle_trim (paths : I → Finset V) (A : Finset V) (B : Finset I) {n p a b : ℕ}
    (ratio : a ≤ b) (aLarge : a*A.card ≤ b*n) (bLarge : a*B.card ≤ b*p) :
    ∃ C ⊆ A, ∃ D ⊆ B, C.card ≤ n ∧ D.card ≤ p ∧
      a^2*rectangleMass paths A B ≤ b^2*rectangleMass paths C D := by
  simpa only [pow_two] using rectangle_trim_ratios paths A B ratio ratio aLarge bLarge

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

omit [LinearOrder I] in
/-- Restricting the vertices and paths cannot increase the incidence mass. -/
theorem rectanglePaths_mass_le [Fintype I] (paths : I → Finset V) (A : Finset V) (B : Finset I) :
    (∑ i : ↥B, (rectanglePaths paths A B i).card) ≤ ∑ i, (paths i).card := by
  rw [rectanglePath_mass]
  unfold rectangleMass
  calc
    _ ≤ ∑ i ∈ B, (paths i).card := sum_le_sum (fun _ _ => card_le_card inter_subset_left)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => Nat.zero_le _)

/-- Restricting the path indices does not increase any vertex degree. -/
theorem rectanglePaths_degree_le [Fintype I] (paths : I → Finset V) (A : Finset V) (B : Finset I) (v : A) :
    (occurrences (rectanglePaths paths A B) v).card ≤ (occurrences paths v.val).card := by
  rw [rectanglePath_degree]
  apply card_le_card
  intro i hi
  exact mem_occurrences.mpr (mem_filter.mp hi).2

/-- Delete vertices and paths below the given minimum degree and length.
The mass lost is at most the sum of the thresholds times the original counts. -/
theorem rectanglePaths_prune (paths : I → Finset V) (A : Finset V) (B : Finset I)
    {d l : ℝ} (d0 : 0 ≤ d) (l0 : 0 ≤ l) :
    ∃ C ⊆ A, ∃ D ⊆ B,
      ((∑ i : B, (rectanglePaths paths A B i).card : ℕ) : ℝ) - d*A.card - l*B.card ≤
        ((∑ i : D, (rectanglePaths paths C D i).card : ℕ) : ℝ) ∧
      (∀ v, d ≤ (occurrences (rectanglePaths paths C D) v).card) ∧
      (∀ i, l ≤ (rectanglePaths paths C D i).card) := by
  obtain ⟨C,cSub,D,dSub,mass,degree,length⟩ := rectangle_prune paths A B d0 l0
  refine ⟨C,cSub,D,dSub,?_,?_,?_⟩
  · simpa only [rectanglePath_mass] using mass
  · intro v
    rw [rectanglePath_degree]
    exact degree v.val v.property
  · intro i
    rw [rectanglePath_card]
    exact length i.val i.property

private def rectangleBridge (paths : I → Finset V) (A : Finset V) (B : Finset I) {k : ℕ}
    (b : Bridge (PathBefore (rectanglePaths paths A B)) k) : Bridge (PathBefore paths) k := by
  have before {i : ↥B} {u v : ↥A} (h : PathBefore (rectanglePaths paths A B) i u v) :
      PathBefore paths i.1 u.1 v.1 :=
    ⟨(mem_filter.mp h.1).2,(mem_filter.mp h.2.1).2,h.2.2⟩
  exact orderedBridge (fun i => (b.vertex i).1) (fun i => (b.arc i).1) b.river.1
    (fun _ _ eq => b.distinctArcs (Subtype.ext eq))
    (fun i eq => b.river_ne_arc i (Subtype.ext eq)) (before b.riverStep) (fun i => before (b.arcStep i))

private theorem rectangleHalfFree {paths : I → Finset V} {size : ℕ} (A : Finset V) (B : Finset I)
    (free : HalfBridgeFree (PathBefore paths) size) :
    HalfBridgeFree (PathBefore (rectanglePaths paths A B)) size := by
  intro k size b earlier
  exact free size (rectangleBridge paths A B b) earlier

omit [LinearOrder I] in
private theorem rectangleFullFree {paths : I → Finset V} {size : ℕ} (A : Finset V) (B : Finset I)
    (free : BridgeFree (PathBefore paths) size) :
    BridgeFree (PathBefore (rectanglePaths paths A B)) size := by
  intro k size
  exact ⟨fun b => (free size).false (rectangleBridge paths A B b)⟩

variable [Fintype V] [Fintype I]

omit [Fintype V] in
/-- When all rows are kept, the mass of a rectangle is the sum of the
degrees of its retained vertices. -/
theorem rectanglePaths_univ_rows_mass (paths : I → Finset V) (A : Finset V) :
    (∑ i : (univ : Finset I), (rectanglePaths paths A univ i).card) =
      ∑ v ∈ A, (occurrences paths v).card := by
  rw [← sum_occurrences]
  calc
    _ = ∑ v : A, (occurrences paths v.val).card :=
      sum_congr rfl (fun v _ => rectanglePath_degree paths A univ v)
    _ = _ := (sum_subtype A (fun _ => Iff.rfl) fun v => (occurrences paths v).card).symm

omit [LinearOrder I] in
theorem rectanglePaths_univ_mass (paths : I → Finset V) :
    ∑ i : (univ : Finset I), (rectanglePaths paths (univ : Finset V) univ i).card = ∑ i, (paths i).card := by
  rw [rectanglePath_mass]
  simp [rectangleMass]

/-- With at least four vertices and four paths, a subfamily within one
quarter of each budget retains at least one forty-ninth of the incidences. -/
theorem rectanglePaths_quarter (paths : I → Finset V)
    (hn : 4 ≤ Fintype.card V) (hp : 4 ≤ Fintype.card I) :
    ∃ A : Finset V, ∃ B : Finset I,
      A.card ≤ Fintype.card V/4 ∧ B.card ≤ Fintype.card I/4 ∧
      (∑ i, (paths i).card) ≤ 49*(∑ i : B, (rectanglePaths paths A B i).card) := by
  have vb : 1*(univ : Finset V).card ≤ 7*(Fintype.card V/4) := by
    rw [card_univ,one_mul]
    omega
  have ib : 1*(univ : Finset I).card ≤ 7*(Fintype.card I/4) := by
    rw [card_univ,one_mul]
    omega
  obtain ⟨A,_,B,_,ac,bc,mass⟩ := rectangle_trim paths univ univ (by decide) vb ib
  refine ⟨A,B,ac,bc,?_⟩
  rw [rectanglePath_mass]
  simpa [rectangleMass] using mass

omit [LinearOrder V] [LinearOrder I] [Fintype V] in
/-- Upper bound on the exact number of block slots. -/
theorem blockIndex_card_precise (sets : I → Finset V) {w : ℕ} (hw : 0 < w) :
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

/-- Width from four times the average, with room to trim back to the budget. -/
theorem four_average_width {M q : ℕ} (hq : 0 < q) (dense : q ≤ M) :
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

/-- Trim by separate vertex and path ratios, then peel at lower caps set by
an original mass. The active incidence rectangle may already have lost mass. -/
theorem balancedRectangle_subsystem_of_ratios_frozen (Z : I → Finset V)
    {n p M vNum vDen pNum pDen retention : ℕ}
    (hn : 0 < n) (hp : 0 < p)
    (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
    (vertices : vNum*Fintype.card V ≤ vDen*n) (families : pNum*Fintype.card I ≤ pDen*p)
    (enough : (vDen*pDen)*(retention+2)*M ≤ 2*(vNum*pNum)*retention*(∑ i, (Z i).card)) :
    ∃ A : Finset V, ∃ B : Finset I,
      let clean := rectanglePaths Z A B
      A.card ≤ n ∧ B.card ≤ p ∧ M ≤ retention * (∑ i, (clean i).card) ∧
        (∀ v, (M : ℝ) / (4 * (n : ℝ)) ≤ (occurrences clean v).card) ∧
        (∀ i, (M : ℝ) / (4 * (p : ℝ)) ≤ (clean i).card) := by
  let A0 : Finset V := univ
  let B0 : Finset I := univ
  let d0 : ℝ := (M : ℝ) / (4 * (n : ℝ))
  let l0 : ℝ := (M : ℝ) / (4 * (p : ℝ))
  have ZMass : rectangleMass Z A0 B0 = ∑ i, (Z i).card := by simp [rectangleMass, A0, B0]
  have vCap : vNum * A0.card ≤ vDen * n := by simpa [A0] using vertices
  have iCap : pNum * B0.card ≤ pDen * p := by simpa [B0] using families
  obtain ⟨A1,_,B1,_,ac,bc,densePart⟩ := rectangle_trim_ratios Z A0 B0 vRatio pRatio vCap iCap
  have d0_nonneg : 0 ≤ d0 := div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have l0_nonneg : 0 ≤ l0 := div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  obtain ⟨A,as,B,bs,keep,minDegree,minLength⟩ := rectanglePaths_prune Z A1 B1 d0_nonneg l0_nonneg
  simp only [rectanglePath_mass] at keep
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
  let a : ℝ := (vNum:ℝ)*(pNum:ℝ)
  let b : ℝ := (vDen:ℝ)*(pDen:ℝ)
  let r : ℝ := retention
  have positive : 0 < b := mul_pos (Nat.cast_pos.mpr vPos) (Nat.cast_pos.mpr pPos)
  have rNonneg : 0 ≤ r := Nat.cast_nonneg _
  have part : a*((∑ i, (Z i).card : ℕ) : ℝ) ≤ b*(rectangleMass Z A1 B1:ℝ) := by
    rw [ZMass] at densePart
    dsimp only [a,b]
    exact_mod_cast densePart
  have loss : (rectangleMass Z A1 B1:ℝ) ≤ (rectangleMass Z A B:ℝ)+(M:ℝ)/2 := by
    linarith only [keep,loseDegree,loseLength]
  have massBound := part.trans (mul_le_mul_of_nonneg_left loss positive.le)
  have budget : b*(r+2)*(M:ℝ) ≤ 2*a*r*((∑ i, (Z i).card : ℕ) : ℝ) := by
    dsimp only [a,b,r]
    exact_mod_cast enough
  have retain : b*(r+2)*(M:ℝ) ≤ (2*r)*(b*((rectangleMass Z A B:ℝ)+(M:ℝ)/2)) := by
    calc
      _ ≤ (2*a*r)*((∑ i, (Z i).card : ℕ) : ℝ) := budget
      _ = (2*r)*(a*((∑ i, (Z i).card : ℕ) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left massBound (by positivity)
  have cancelled : (2*b)*(M:ℝ) ≤ (2*b)*(r*(rectangleMass Z A B:ℝ)) := by
    apply (add_le_add_iff_right (b*r*(M:ℝ))).mp
    calc
      _ = b*(r+2)*(M:ℝ) := by ring
      _ ≤ _ := retain
      _ = _ := by ring
  have finalMass : M ≤ retention*(∑ i, (clean i).card) := by
    rw [rectanglePath_mass]
    have h := (mul_le_mul_iff_right₀ (by positivity : 0 < 2*b)).mp cancelled
    change (M:ℝ) ≤ (retention:ℝ)*(rectangleMass Z A B:ℝ) at h
    exact_mod_cast h
  exact ⟨A, B, (card_le_card as).trans ac, (card_le_card bs).trans bc, finalMass, minDegree, minLength⟩

/-- Trim by separate vertex and path ratios, then peel at the frozen lower caps. -/
theorem balancedRectangle_subsystem_of_ratios (Z : I → Finset V) {n p vNum vDen pNum pDen retention : ℕ}
    (hn : 0 < n) (hp : 0 < p)
    (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
    (vertices : vNum*Fintype.card V ≤ vDen*n) (families : pNum*Fintype.card I ≤ pDen*p)
    (enough : (vDen*pDen)*(retention+2) ≤ 2*(vNum*pNum)*retention) :
    let M := ∑ i, (Z i).card
    ∃ A : Finset V, ∃ B : Finset I,
      let clean := rectanglePaths Z A B
      A.card ≤ n ∧ B.card ≤ p ∧ M ≤ retention * (∑ i, (clean i).card) ∧
        (∀ v, (M : ℝ) / (4 * (n : ℝ)) ≤ (occurrences clean v).card) ∧
        (∀ i, (M : ℝ) / (4 * (p : ℝ)) ≤ (clean i).card) :=
  balancedRectangle_subsystem_of_ratios_frozen Z hn hp vPos pPos vRatio pRatio vertices families
    (Nat.mul_le_mul_right _ enough)

/-- Trim an incidence rectangle to the requested budgets and erase low
rows and columns. The argument depends only on membership. -/
theorem balancedRectangle_subsystem (Z : I → Finset V) {n p : ℕ}
    (hn : 0 < n) (hp : 0 < p)
    (vertices : 3 * Fintype.card V ≤ 4 * n) (families : 3 * Fintype.card I ≤ 4 * p) :
    let M := ∑ i, (Z i).card
    ∃ A : Finset V, ∃ B : Finset I,
      let clean := rectanglePaths Z A B
      A.card ≤ n ∧ B.card ≤ p ∧ M ≤ 16 * (∑ i, (clean i).card) ∧
        (∀ v, (M : ℝ) / (4 * (n : ℝ)) ≤ (occurrences clean v).card) ∧
        (∀ i, (M : ℝ) / (4 * (p : ℝ)) ≤ (clean i).card) :=
  balancedRectangle_subsystem_of_ratios Z hn hp (by decide) (by decide) (by decide) (by decide)
    vertices families (by decide)

/-- Incidence mass at least three times the budget leaves room for synchronized cuts. -/
theorem three_dense_width {M q : ℕ} (hq : 0 < q) (dense : 3*q ≤ M) :
    let width := 4*M/q
    0 < width ∧ 11*(M/width) ≤ 3*q ∧ (width:ℝ) ≤ 4*(M:ℝ)/(q:ℝ) := by
  let width := 4*M/q
  obtain ⟨positive, _, cap⟩ := four_average_width hq (show q ≤ M by omega)
  have raw := Nat.lt_mul_div_succ (4*M) hq
  change 4*M < q*(width+1) at raw
  rw [Nat.mul_succ] at raw
  have sufficient : 11*M ≤ 3*(q*width) := by omega
  refine ⟨positive, ?_, cap⟩
  apply Nat.le_of_mul_le_mul_right _ positive
  calc
    _ = 11*((M/width)*width) := by ring
    _ ≤ 11*M := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ ≤ 3*(q*width) := sufficient
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- With a common vertex order and incidence mass at least both original counts,
splitting, restriction, and pruning meet both budgets and all four average caps.
The surviving mass is at least a sixteenth of the original mass. Every
full or half-bridge size exclusion of the input is preserved. -/
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
        (∀ size, HalfBridgeFree (PathBefore paths) size → HalfBridgeFree (PathBefore clean) size) ∧
        (∀ size, BridgeFree (PathBefore paths) size → BridgeFree (PathBefore clean) size) := by
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
  have total : (∑ i, (Z i).card) = M := (splitPaths_size s l).trans sMass
  obtain ⟨A, B, ac, bc, finalMass, minDegree, minLength⟩ := balancedRectangle_subsystem Z hn hp
    (by simpa only [A0, card_univ] using vertices) (by simpa only [B0, card_univ] using families)
  rw [total] at finalMass minDegree minLength
  let clean := rectanglePaths Z A B
  refine ⟨A, B, ac, bc, finalMass, ?_, ?_,
    fun _ free => rectangleHalfFree A B (regularization_halfFree free d l),
    fun _ free => rectangleFullFree A B (regularization_free free d l)⟩
  · intro v
    change d0 ≤ ((occurrences clean v).card : ℝ) ∧
      ((occurrences clean v).card : ℝ) ≤ 4 * (M : ℝ) / (n : ℝ)
    refine ⟨minDegree v, ?_⟩
    have cap := ((rectanglePaths_degree_le Z A B v).trans (splitPaths_degree s l v.1)).trans
      (splitVertices_degree paths hd v.1)
    exact (Nat.cast_le.mpr cap).trans dCap
  · intro i
    change l0 ≤ ((clean i).card : ℝ) ∧ ((clean i).card : ℝ) ≤ 4 * (M : ℝ) / (p : ℝ)
    rw [show (clean i).card = (Z i.1 ∩ A).card from rectanglePath_card Z A B i]
    refine ⟨(rectanglePath_card Z A B i) ▸ minLength i, ?_⟩
    have cap := (card_le_card (inter_subset_left : Z i.1 ∩ A ⊆ Z i.1)).trans
      (splitPaths_length s hl i.1)
    exact (Nat.cast_le.mpr cap).trans lCap

end Ordered

private theorem sum_part_and_remainder {A : Type*} [DecidableEq A] (whole part : Finset A)
    (sub : part ⊆ whole) (weight : A → ℕ) :
    (∑ x ∈ part, weight x)+(∑ x ∈ whole \ part, weight x) = ∑ x ∈ whole, weight x := by
  have disjoint : Disjoint part (whole \ part) := disjoint_left.mpr fun _ hpart hrest => (mem_sdiff.mp hrest).2 hpart
  have join : part ∪ (whole \ part) = whole := by
    ext x
    simp only [mem_union,mem_sdiff]
    constructor
    · rintro (h | h)
      · exact sub h
      · exact h.1
    · intro h
      by_cases inside : x ∈ part
      · exact Or.inl inside
      · exact Or.inr ⟨h,inside⟩
  rw [← sum_union disjoint,join]

/-- Keep the designated blocks of weight at least the width, then
retain the heaviest remainders. The loss is bounded by the square
of the total weight divided by four times the budget capacity. -/
theorem trim_full_weight_blocks_quadratic_of_lower_bound {A : Type*}
    [DecidableEq A] [Fintype A] (weight : A → ℕ)
    (full : Finset A) {cap budget : ℕ} (capPositive : 0 < cap)
    (filled : ∀ x ∈ full, cap ≤ weight x) (remainder : (univ \ full).card ≤ budget)
    (space : (∑ x, weight x) ≤ cap*budget) :
    let total := ∑ x, weight x
    ∃ kept : Finset A, kept.card ≤ budget ∧
      4*(cap*budget)*(∑ x ∈ univ \ kept, weight x) ≤ total^2 := by
  classical
  by_cases all : (univ : Finset A).card ≤ budget
  · exact ⟨univ,all,by simp⟩
  let K := ∑ x, weight x
  let rest := univ \ full
  let R := ∑ x ∈ rest, weight x
  let f := full.card
  have fullWeight : f*cap ≤ (∑ x ∈ full, weight x) := by
    rw [show f*cap = ∑ _ ∈ full, cap by simp [f]]
    exact sum_le_sum filled
  have total : f*cap+R ≤ K := by
    have eq : R+(∑ x ∈ full, weight x) = K := sum_sdiff (subset_univ full)
    omega
  have fLe : f ≤ budget := by
    apply Nat.le_of_mul_le_mul_right _ capPositive
    calc
      f*cap ≤ K := by omega
      _ ≤ cap*budget := space
      _ = budget*cap := Nat.mul_comm _ _
  obtain ⟨selected,selectedSub,selectedCount,chosenBound⟩ :=
    trim_weights_ratio rest weight (n := budget-f) (a := budget-f) (b := budget)
      (Nat.sub_le _ _) ((Nat.mul_le_mul_left (budget-f) remainder).trans_eq (Nat.mul_comm _ _))
  let kept := full ∪ selected
  let loss := ∑ x ∈ rest \ selected, weight x
  let chosenWeight := ∑ x ∈ selected, weight x
  have disjoint : Disjoint full selected := disjoint_left.mpr fun x xFull xSelected =>
    (mem_sdiff.mp (selectedSub xSelected)).2 xFull
  have keptCount : kept.card ≤ budget := by
    rw [show kept = full ∪ selected from rfl,card_union_of_disjoint disjoint]
    change f+selected.card ≤ budget
    omega
  have removedSet : univ \ kept = rest \ selected := by
    ext x
    simp [kept,rest,not_or]
  have split : loss+chosenWeight = R := sum_sdiff selectedSub
  change (budget-f)*R ≤ budget*chosenWeight at chosenBound
  have less : budget*loss ≤ f*R := by
    have whole : budget*loss+budget*chosenWeight = budget*R := by rw [← Nat.mul_add,split]
    have available : f*R+(budget-f)*R = budget*R := by rw [← Nat.add_mul,Nat.add_sub_of_le fLe]
    omega
  have product : 4*(f*cap)*R ≤ K^2 := by
    calc
      _ ≤ (f*cap+R)^2 := by
        have sq : 4*((f*cap:ℕ):ℤ)*(R:ℤ) ≤ (((f*cap:ℕ):ℤ)+(R:ℤ))^2 := by
          nlinarith only [sq_nonneg (((f*cap:ℕ):ℤ)-(R:ℤ))]
        exact_mod_cast sq
      _ ≤ _ := Nat.pow_le_pow_left total 2
  refine ⟨kept,keptCount,?_⟩
  rw [removedSet]
  calc
    4*(cap*budget)*loss = 4*cap*(budget*loss) := by ring
    _ ≤ 4*cap*(f*R) := Nat.mul_le_mul_left _ less
    _ = 4*(f*cap)*R := by ring
    _ ≤ K^2 := product

/-- Keep the filled blocks and the heaviest remainders. The loss is
at most the squared total weight divided by four times the budget capacity. -/
theorem trim_full_weight_blocks_quadratic {A : Type*} [DecidableEq A] [Fintype A] (weight : A → ℕ)
    (full : Finset A) {cap budget : ℕ} (capPositive : 0 < cap)
    (filled : ∀ x ∈ full, weight x = cap) (remainder : (univ \ full).card ≤ budget)
    (space : (∑ x, weight x) ≤ cap*budget) :
    let total := ∑ x, weight x
    ∃ kept : Finset A, kept.card ≤ budget ∧ 4*(cap*budget)*(∑ x ∈ univ \ kept, weight x) ≤ total^2 :=
  trim_full_weight_blocks_quadratic_of_lower_bound weight full capPositive
    (fun x h => (filled x h).ge) remainder space

/-- If the budget capacity is at least three times the total weight,
at most one twelfth of the weight is omitted. -/
theorem trim_full_weight_blocks {A : Type*} [DecidableEq A] [Fintype A] (weight : A → ℕ)
    (full : Finset A) {cap budget : ℕ} (capPositive : 0 < cap) (budgetPositive : 0 < budget)
    (filled : ∀ x ∈ full, weight x = cap) (remainder : (univ \ full).card ≤ budget)
    (space : 3*(∑ x, weight x) ≤ cap*budget) :
    ∃ kept : Finset A, kept.card ≤ budget ∧ 12*(∑ x ∈ univ \ kept, weight x) ≤ ∑ x, weight x := by
  let K := ∑ x, weight x
  have room : K ≤ cap*budget := by change 3*K ≤ _ at space; omega
  obtain ⟨kept,count,lossBound⟩ := trim_full_weight_blocks_quadratic weight full capPositive filled remainder room
  let loss := ∑ x ∈ univ \ kept, weight x
  refine ⟨kept,count,Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos capPositive budgetPositive)⟩
  calc
    (12*loss)*(cap*budget) = 3*(4*(cap*budget)*loss) := by ring
    _ ≤ 3*K^2 := Nat.mul_le_mul_left _ lossBound
    _ = K*(3*K) := by ring
    _ ≤ K*(cap*budget) := Nat.mul_le_mul_left _ space

/-- Trim filled vertex blocks before the remainders while retaining all
path rows. Record the exact lost mass and its quadratic bound. -/
theorem trim_full_vertex_blocks_quadratic {V I : Type*} [Fintype V] [Fintype I] [LinearOrder V] [DecidableEq I]
    (paths : I → Finset V) (filled : Finset V) {width budget : ℕ} (positive : 0 < width)
    (full : ∀ v ∈ filled, (occurrences paths v).card = width) (rest : (univ \ filled).card ≤ budget)
    (space : (∑ i, (paths i).card) ≤ width*budget) :
    let K := ∑ i, (paths i).card
    ∃ A : Finset V, A.card ≤ budget ∧ ∃ loss : ℕ, 4*(width*budget)*loss ≤ K^2 ∧
      (∑ i : (univ : Finset I), (rectanglePaths paths A univ i).card)+loss = K := by
  have room : (∑ v, (occurrences paths v).card) ≤ width*budget := by rw [sum_occurrences]; exact space
  obtain ⟨A,cap,lossBound⟩ := trim_full_weight_blocks_quadratic (fun v => (occurrences paths v).card)
    filled positive full rest room
  rw [sum_occurrences] at lossBound
  refine ⟨A,cap,_,lossBound,?_⟩
  rw [rectanglePath_mass,← show rectangleMass paths A univ = _ from rfl,rectangleMass_swap,← sum_occurrences]
  exact sum_part_and_remainder univ A (subset_univ _) _

/-- If each dimension consists of cap-sized blocks and at most one
remainder per original slot, trimming to both budgets retains at least
five sixths of the total incidence mass. -/
theorem trim_full_block_rectangles {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (paths : I → Finset V) (fullV : Finset V) (fullI : Finset I) {D L n p : ℕ}
    (Dpos : 0 < D) (Lpos : 0 < L) (hn : 0 < n) (hp : 0 < p)
    (filledV : ∀ v ∈ fullV, (occurrences paths v).card = D) (restV : (univ \ fullV).card ≤ n)
    (filledI : ∀ i ∈ fullI, (paths i).card = L) (restI : (univ \ fullI).card ≤ p)
    (spaceV : 3*(∑ i, (paths i).card) ≤ D*n) (spaceI : 3*(∑ i, (paths i).card) ≤ L*p) :
    ∃ A : Finset V, ∃ B : Finset I, A.card ≤ n ∧ B.card ≤ p ∧
      5*(∑ i, (paths i).card) ≤ 6*(∑ i ∈ B, (paths i ∩ A).card) := by
  let K := ∑ i, (paths i).card
  have spaceColumns : 3*(∑ v, (occurrences paths v).card) ≤ D*n := by rw [sum_occurrences]; exact spaceV
  obtain ⟨A,capA,lossA⟩ := trim_full_weight_blocks (fun v => (occurrences paths v).card) fullV
    Dpos hn filledV restV spaceColumns
  obtain ⟨B,capB,lossB⟩ := trim_full_weight_blocks (fun i => (paths i).card) fullI Lpos hp filledI restI spaceI
  rw [sum_occurrences] at lossA
  let lessV := ∑ v ∈ univ \ A, (occurrences paths v).card
  let lessI := ∑ i ∈ univ \ B, (paths i).card
  let kept := rectangleMass paths A B
  have columns : rectangleMass paths A univ+lessV = K := by
    rw [rectangleMass_swap]
    change (∑ v ∈ A, (occurrences paths v).card)+lessV = ∑ i, (paths i).card
    rw [← sum_occurrences paths]
    exact sum_part_and_remainder univ A (subset_univ _) _
  have rows : rectangleMass paths A univ ≤ kept+lessI := by
    have sum := sum_part_and_remainder univ B (subset_univ _) (fun i => (paths i ∩ A).card)
    change kept+(∑ i ∈ univ \ B, (paths i ∩ A).card) = rectangleMass paths A univ at sum
    rw [← sum]
    exact Nat.add_le_add_left (sum_le_sum fun i _ => card_le_card inter_subset_left) _
  change 12*lessV ≤ K at lossA
  change 12*lessI ≤ K at lossB
  refine ⟨A,B,capA,capB,?_⟩
  change 5*K ≤ 6*kept
  omega

end OnlineReachabilityPreservers
