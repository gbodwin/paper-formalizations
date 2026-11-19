import OnlineReachabilityPreservers.Basic

/-! Weighted cut covering for the auxiliary forest construction. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The unnormalized product of edge cost and capacity after a number of charges.
Between two doublings it increases linearly. -/
def weightedLoad (cost charge : ℕ) : ℕ :=
  2 ^ (charge / cost) * (cost + charge % cost)

def weightedCapacity (cost charge : ℕ) : ℚ :=
  (weightedLoad cost charge : ℚ) / (cost : ℚ)

theorem weightedLoad_succ {cost : ℕ} (positive : 0 < cost) (charge : ℕ) :
    weightedLoad cost (charge + 1) = weightedLoad cost charge + 2 ^ (charge / cost) := by
  have split := Nat.mod_add_div charge cost
  have rem := Nat.mod_lt charge positive
  by_cases carry : charge % cost + 1 < cost
  · have qr : (charge + 1) / cost = charge / cost ∧ (charge + 1) % cost = charge % cost + 1 :=
      (Nat.div_mod_unique positive).mpr ⟨by omega, carry⟩
    simp only [weightedLoad, qr.1, qr.2]
    ring
  · have next : charge % cost + 1 = cost := by omega
    have qr : (charge + 1) / cost = charge / cost + 1 ∧ (charge + 1) % cost = 0 :=
      (Nat.div_mod_unique positive).mpr ⟨by rw [Nat.mul_add, Nat.mul_one]; omega, positive⟩
    simp only [weightedLoad, qr.1, qr.2, Nat.add_zero, pow_succ]
    generalize 2 ^ (charge / cost) = base
    generalize charge % cost = remainder at next ⊢
    rw [← next]
    ring

theorem weightedLoad_mono {cost : ℕ} (positive : 0 < cost) : Monotone (weightedLoad cost) :=
  monotone_nat_of_le_succ fun i => (weightedLoad_succ positive i).symm ▸ Nat.le_add_right _ _

theorem weightedCapacity_mono {cost : ℕ} (positive : 0 < cost) : Monotone (weightedCapacity cost) := by
  intro a b hab
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (weightedLoad_mono positive hab)) (by positivity)

theorem weightedCapacity_nonneg (cost charge : ℕ) : 0 ≤ weightedCapacity cost charge := by
  unfold weightedCapacity
  positivity

theorem weightedCapacity_ge_pow {cost : ℕ} (positive : 0 < cost) (charge : ℕ) :
    ((2 ^ (charge / cost) : ℕ) : ℚ) ≤ weightedCapacity cost charge := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr positive)).mpr
  norm_cast
  exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

section Updates

variable {E : Type*} [DecidableEq E]

/-- Add one charge to each edge in the current violated cut. -/
def chargeWeightedCut (cut : Finset E) (charges : E → ℕ) (e : E) : ℕ :=
  charges e + if e ∈ cut then 1 else 0

theorem le_chargeWeightedCut (cut : Finset E) (charges : E → ℕ) : charges ≤ chargeWeightedCut cut charges :=
  fun _ => Nat.le_add_right _ _

def weightedObjective (edges : Finset E) (weight charges : E → ℕ) : ℕ :=
  ∑ e ∈ edges, weightedLoad (weight e) (charges e)

def weightedCutSum (cut : Finset E) (weight charges : E → ℕ) : ℚ :=
  ∑ e ∈ cut, weightedCapacity (weight e) (charges e)

theorem chargeWeightedCut_objective_le {edges cut : Finset E}
    (sub : cut ⊆ edges) (weight charges : E → ℕ)
    (positive : ∀ e ∈ edges, 0 < weight e) :
    (weightedObjective edges weight (chargeWeightedCut cut charges) : ℚ) ≤
      (weightedObjective edges weight charges : ℚ) + weightedCutSum cut weight charges := by
  have atEdge (e : E) (he : e ∈ edges) :
      weightedLoad (weight e) (chargeWeightedCut cut charges e) =
        weightedLoad (weight e) (charges e) + if e ∈ cut then 2 ^ (charges e / weight e) else 0 := by
    by_cases h : e ∈ cut
    · simp [chargeWeightedCut, h, weightedLoad_succ (positive e he)]
    · simp [chargeWeightedCut, h]
  have objective_eq :
      weightedObjective edges weight (chargeWeightedCut cut charges) =
        weightedObjective edges weight charges + ∑ e ∈ cut, 2 ^ (charges e / weight e) := by
    unfold weightedObjective
    rw [sum_congr rfl atEdge, sum_add_distrib, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr sub]
  rw [objective_eq, Nat.cast_add, Nat.cast_sum]
  exact add_le_add le_rfl (sum_le_sum fun e he => weightedCapacity_ge_pow (positive e (sub he)) (charges e))

theorem chargeWeightedCut_bounded {edges cut : Finset E} (weight charges : E → ℕ) (scale : ℕ)
    (scalePos : 0 < scale) (positive : ∀ e ∈ edges, 0 < weight e)
    (small : weightedCutSum cut weight charges < (scale : ℚ))
    (before : ∀ e ∈ edges, charges e ≤ (scale.log2 + 1) * weight e) :
    ∀ e ∈ edges, chargeWeightedCut cut charges e ≤ (scale.log2 + 1) * weight e := by
  intro e he
  by_cases hit : e ∈ cut
  · have level : ((2 ^ (charges e / weight e) : ℕ) : ℚ) ≤ weightedCutSum cut weight charges :=
      (weightedCapacity_ge_pow (positive e he) _).trans
        (single_le_sum (f := fun z => weightedCapacity (weight z) (charges z))
          (fun z _ => weightedCapacity_nonneg _ _) hit)
    have dichotomy : 2 ^ (charges e / weight e) ≤ scale := by exact_mod_cast (level.trans small.le)
    have exponent : charges e / weight e ≤ scale.log2 := (Nat.le_log2 scalePos.ne').mpr dichotomy
    have steps : charges e < (scale.log2 + 1) * weight e :=
      (Nat.div_lt_iff_lt_mul (positive e he)).mp (Nat.lt_succ_of_le exponent)
    simpa [chargeWeightedCut, hit] using Nat.succ_le_of_lt steps
  · simpa [chargeWeightedCut, hit] using before e he

theorem chargeWeightedCut_sum (cut chosen : Finset E) (charges : E → ℕ) :
    (∑ e ∈ chosen, chargeWeightedCut cut charges e) =
      (∑ e ∈ chosen, charges e) + (chosen ∩ cut).card := by
  simp only [chargeWeightedCut, sum_add_distrib]
  rw [← sum_filter, filter_mem_eq_inter]
  simp

/-- A list of accepted updates, each triggered by a violated cut and
followed by an irrevocable capacity raise. -/
inductive WeightedCutUpdates (weight : E → ℕ) (scale : ℕ) :
    (E → ℕ) → List (Finset E) → (E → ℕ) → Prop
  | nil (loads : E → ℕ) : WeightedCutUpdates weight scale loads [] loads
  | cons {loads final : E → ℕ} {cut : Finset E} {cuts : List (Finset E)}
      (violation : weightedCutSum cut weight loads < (scale : ℚ))
      (rest : WeightedCutUpdates weight scale (chargeWeightedCut cut loads) cuts final) :
      WeightedCutUpdates weight scale loads (cut :: cuts) final

theorem WeightedCutUpdates.bound {weight : E → ℕ} {scale : ℕ} {initial final : E → ℕ}
    {cuts : List (Finset E)} (updates : WeightedCutUpdates weight scale initial cuts final)
    (edges chosen : Finset E) (positive : ∀ e ∈ edges, 0 < weight e)
    (scalePos : 0 < scale) (sub : ∀ cut ∈ cuts, cut ⊆ edges)
    (touch : ∀ cut ∈ cuts, (chosen ∩ cut).Nonempty)
    (initialCap : ∀ e ∈ edges, initial e ≤ (scale.log2 + 1) * weight e) :
    initial ≤ final ∧
      (∀ e ∈ edges, final e ≤ (scale.log2 + 1) * weight e) ∧
      (∑ e ∈ chosen, initial e) + cuts.length ≤ ∑ e ∈ chosen, final e ∧
      (weightedObjective edges weight final : ℚ) ≤ weightedObjective edges weight initial +
        (scale : ℚ) * (cuts.length : ℚ) := by
  induction updates with
  | nil => simpa using initialCap
  | @cons current result cut rest small updates ih =>
    have cs := sub cut List.mem_cons_self
    have touched := card_pos.mpr (touch cut List.mem_cons_self)
    obtain ⟨mono, bound, charge, obj⟩ := ih
      (fun c hc => sub c (List.mem_cons_of_mem _ hc)) (fun c hc => touch c (List.mem_cons_of_mem _ hc))
      (chargeWeightedCut_bounded weight current scale scalePos positive small initialCap)
    have changeWeight := chargeWeightedCut_objective_le cs weight current positive
    have changeCharge := chargeWeightedCut_sum cut chosen current
    refine ⟨(le_chargeWeightedCut cut current).trans mono, bound, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      linarith only [obj, changeWeight, small]

/-- The total weighted fractional cost of all accepted cut updates. The
initial capacity is scaled by the total cost of the edges. -/
theorem WeightedCutUpdates.competitive {weight : E → ℕ} {final : E → ℕ}
    {cuts : List (Finset E)} (edges chosen : Finset E) (chosenSub : chosen ⊆ edges)
    (positive : ∀ e ∈ edges, 0 < weight e)
    (updates : WeightedCutUpdates weight (max 1 (∑ e ∈ edges, weight e)) (fun _ => 0) cuts final)
    (sub : ∀ cut ∈ cuts, cut ⊆ edges) (touch : ∀ cut ∈ cuts, (chosen ∩ cut).Nonempty) :
    let scale := max 1 (∑ e ∈ edges, weight e)
    cuts.length ≤ (scale.log2 + 1) * (∑ e ∈ chosen, weight e) ∧
      (weightedObjective edges weight final : ℚ) / (scale : ℚ) ≤
        1 + ((scale.log2 + 1 : ℕ) : ℚ) * (∑ e ∈ chosen, (weight e : ℚ)) := by
  let scale := max 1 (∑ e ∈ edges, weight e)
  have scalePos : 0 < scale := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨_, cap, c, obj⟩ := updates.bound edges chosen positive scalePos sub touch
    (fun _ _ => Nat.zero_le _)
  have steps : cuts.length ≤ (scale.log2 + 1) * ∑ e ∈ chosen, weight e := by
    simp only [sum_const_zero, zero_add] at c
    calc
      _ ≤ ∑ e ∈ chosen, final e := c
      _ ≤ ∑ e ∈ chosen, (scale.log2 + 1) * weight e := sum_le_sum fun e he => cap e (chosenSub he)
      _ = _ := (mul_sum ..).symm
  refine ⟨steps, ?_⟩
  have initial : weightedObjective edges weight (fun _ => 0) ≤ scale := by
    simp [weightedObjective, weightedLoad, scale]
  have initialR : (weightedObjective edges weight (fun _ => 0) : ℚ) ≤ (scale : ℚ) := by
    exact_mod_cast initial
  have stepR : (cuts.length : ℚ) ≤
      ((scale.log2 + 1 : ℕ) : ℚ) * (∑ e ∈ chosen, (weight e : ℚ)) := by
    exact_mod_cast steps
  apply (div_le_iff₀ (Nat.cast_pos.mpr scalePos)).mpr
  have h := mul_le_mul_of_nonneg_left stepR (show (0 : ℚ) ≤ scale by positivity)
  linarith only [obj, initialR, h]

theorem WeightedCutUpdates.append {weight : E → ℕ} {scale : ℕ} {initial middle final : E → ℕ}
    {before after : List (Finset E)}
    (first : WeightedCutUpdates weight scale initial before middle)
    (last : WeightedCutUpdates weight scale middle after final) :
    WeightedCutUpdates weight scale initial (before ++ after) final := by
  induction first with
  | nil => exact last
  | cons small _ ih => exact .cons small (ih last)

/-- An explicit separator for an already listed collection of covering cuts. -/
def firstUncoveredWeightedCut (weight : E → ℕ) (scale : ℕ) (cuts : List (Finset E)) (charges : E → ℕ) :
    Option (Finset E) :=
  cuts.find? fun cut => decide (weightedCutSum cut weight charges < (scale : ℚ))

omit [DecidableEq E] in
private theorem firstUncoveredWeightedCut_some {weight : E → ℕ} {scale : ℕ} {cuts : List (Finset E)}
    {charges : E → ℕ} {cut : Finset E} (answer : firstUncoveredWeightedCut weight scale cuts charges = some cut) :
    cut ∈ cuts ∧ weightedCutSum cut weight charges < (scale : ℚ) := by
  unfold firstUncoveredWeightedCut at answer
  have value : decide (weightedCutSum cut weight charges < (scale : ℚ)) = true :=
    List.find?_some (p := fun c : Finset E => decide (weightedCutSum c weight charges < (scale : ℚ))) answer
  exact ⟨List.mem_of_find?_eq_some answer, of_decide_eq_true value⟩

omit [DecidableEq E] in
private theorem firstUncoveredWeightedCut_none {weight : E → ℕ} {scale : ℕ} {cuts : List (Finset E)}
    {charges : E → ℕ} (answer : firstUncoveredWeightedCut weight scale cuts charges = none) :
    ∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight charges := by
  unfold firstUncoveredWeightedCut at answer
  intro cut h
  exact le_of_not_gt fun small => (List.find?_eq_none.mp answer cut h) (decide_eq_true small)

/-- Raise capacities through successive separating cuts. The returned list
records the actual updates. -/
def weightedCoverLoop (search : (E → ℕ) → Option (Finset E)) :
    ℕ → (E → ℕ) → (E → ℕ) × List (Finset E)
  | 0, charges => (charges, [])
  | fuel + 1, charges =>
    match search charges with
    | none => (charges, [])
    | some cut =>
      let out := weightedCoverLoop search fuel (chargeWeightedCut cut charges)
      (out.1, cut :: out.2)

theorem weightedCoverLoop_certify (weight : E → ℕ) (scale : ℕ)
    (search : (E → ℕ) → Option (Finset E)) (admissible : Finset E → Prop)
    (covered : (E → ℕ) → Prop)
    (sound : ∀ {charges cut}, search charges = some cut →
      admissible cut ∧ weightedCutSum cut weight charges < (scale : ℚ))
    (complete : ∀ {charges}, search charges = none → covered charges)
    (fuel : ℕ) (initial : E → ℕ) :
    let out := weightedCoverLoop search fuel initial
    WeightedCutUpdates weight scale initial out.2 out.1 ∧ (∀ cut ∈ out.2, admissible cut) ∧
      (out.2.length < fuel → covered out.1) := by
  induction fuel generalizing initial with
  | zero =>
    exact ⟨.nil _, fun _ h => (List.not_mem_nil h).elim, fun h => (Nat.not_lt_zero _ h).elim⟩
  | succ fuel ih =>
    cases response : search initial with
    | none =>
      simpa only [weightedCoverLoop, response] using
        And.intro (WeightedCutUpdates.nil initial)
          ⟨(by simp : ∀ cut ∈ ([] : List (Finset E)), admissible cut), fun _ => complete response⟩
    | some cut =>
      obtain ⟨member, small⟩ := sound response
      obtain ⟨trace, selected, closed⟩ := ih (chargeWeightedCut cut initial)
      simp only [weightedCoverLoop, response]
      refine ⟨.cons small trace, ?_, fun early => closed (Nat.lt_of_succ_lt_succ early)⟩
      intro c present
      rcases List.mem_cons.mp present with rfl | earlier
      · exact member
      · exact selected c earlier

theorem weightedCoverLoop_spec (weight : E → ℕ) (scale : ℕ) (cuts : List (Finset E))
    (search : (E → ℕ) → Option (Finset E))
    (sound : ∀ {charges cut}, search charges = some cut →
      cut ∈ cuts ∧ weightedCutSum cut weight charges < (scale : ℚ))
    (complete : ∀ {charges}, search charges = none →
      ∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight charges)
    (fuel : ℕ) (initial : E → ℕ) :
    let out := weightedCoverLoop search fuel initial
    WeightedCutUpdates weight scale initial out.2 out.1 ∧ (∀ cut ∈ out.2, cut ∈ cuts) ∧
      (out.2.length < fuel → ∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight out.1) :=
  weightedCoverLoop_certify weight scale search (fun cut => cut ∈ cuts)
    (fun charges => ∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight charges)
    sound complete fuel initial

/-- The initial fractional cost is at most one with this normalization. -/
def weightedCoverScale (edges : Finset E) (weight : E → ℕ) : ℕ :=
  max 1 (∑ e ∈ edges, weight e)

def weightedCoverFuel (edges : Finset E) (weight : E → ℕ) : ℕ :=
  ((weightedCoverScale edges weight).log2 + 1) * (∑ e ∈ edges, weight e) + 1

def weightedCoverStep (edges : Finset E) (weight : E → ℕ) (cuts : List (Finset E))
    (initial : E → ℕ) : (E → ℕ) × List (Finset E) :=
  weightedCoverLoop (firstUncoveredWeightedCut weight (weightedCoverScale edges weight) cuts)
    (weightedCoverFuel edges weight) initial

theorem weightedCoverStep_spec (edges : Finset E) (weight : E → ℕ) (cuts : List (Finset E))
    (positive : ∀ e ∈ edges, 0 < weight e)
    (valid : ∀ cut ∈ cuts, cut ⊆ edges ∧ cut.Nonempty)
    (initial : E → ℕ)
    (bounded : ∀ e ∈ edges, initial e ≤ ((weightedCoverScale edges weight).log2 + 1) * weight e) :
    let scale := weightedCoverScale edges weight
    let out := weightedCoverStep edges weight cuts initial
    initial ≤ out.1 ∧ (∀ e ∈ edges, out.1 e ≤ (scale.log2 + 1) * weight e) ∧
      WeightedCutUpdates weight scale initial out.2 out.1 ∧ (∀ cut ∈ out.2, cut ∈ cuts) ∧
      (∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight out.1) := by
  let scale := weightedCoverScale edges weight
  let out := weightedCoverStep edges weight cuts initial
  have scalePos : 0 < scale := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨trace, selected, done⟩ :=
    weightedCoverLoop_spec weight scale cuts _ firstUncoveredWeightedCut_some firstUncoveredWeightedCut_none
      (weightedCoverFuel edges weight) initial
  change WeightedCutUpdates weight scale initial out.2 out.1 at trace
  change ∀ cut ∈ out.2, cut ∈ cuts at selected
  change out.2.length < weightedCoverFuel edges weight →
    ∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight out.1 at done
  have sub : ∀ cut ∈ out.2, cut ⊆ edges := fun c hc => (valid c (selected c hc)).1
  have touch : ∀ cut ∈ out.2, (edges ∩ cut).Nonempty := by
    intro c hc
    rw [inter_eq_right.mpr (sub c hc)]
    exact (valid c (selected c hc)).2
  obtain ⟨mono, cap, steps, _⟩ := trace.bound edges edges positive scalePos sub touch bounded
  have fuel : out.2.length < weightedCoverFuel edges weight := by
    have upper : ∑ e ∈ edges, out.1 e ≤ (scale.log2 + 1) * (∑ e ∈ edges, weight e) := by
      rw [mul_sum]
      exact sum_le_sum cap
    change out.2.length < (scale.log2 + 1) * (∑ e ∈ edges, weight e) + 1
    omega
  exact ⟨mono, cap, trace, selected, done fuel⟩

/-- Process batches of cuts in arrival order while retaining previous capacities. -/
def weightedCoverRun (edges : Finset E) (weight : E → ℕ) :
    List (List (Finset E)) → (E → ℕ) → (E → ℕ) × List (Finset E)
  | [], initial => (initial, [])
  | cuts :: batches, initial =>
    let first := weightedCoverStep edges weight cuts initial
    let rest := weightedCoverRun edges weight batches first.1
    (rest.1, first.2 ++ rest.2)

theorem weightedCoverRun_spec (edges : Finset E) (weight : E → ℕ) (batches : List (List (Finset E)))
    (positive : ∀ e ∈ edges, 0 < weight e)
    (valid : ∀ cuts ∈ batches, ∀ cut ∈ cuts, cut ⊆ edges ∧ cut.Nonempty)
    (initial : E → ℕ)
    (bounded : ∀ e ∈ edges, initial e ≤ ((weightedCoverScale edges weight).log2 + 1) * weight e) :
    let scale := weightedCoverScale edges weight
    let out := weightedCoverRun edges weight batches initial
    initial ≤ out.1 ∧ (∀ e ∈ edges, out.1 e ≤ (scale.log2 + 1) * weight e) ∧
      WeightedCutUpdates weight scale initial out.2 out.1 ∧
      (∀ cut ∈ out.2, ∃ cuts ∈ batches, cut ∈ cuts) ∧
      (∀ cuts ∈ batches, ∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight out.1) := by
  induction batches generalizing initial with
  | nil =>
    exact ⟨le_rfl, bounded, .nil _, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | cons cuts batches ih =>
    have Vfirst := valid cuts List.mem_cons_self
    obtain ⟨raise, cap, firstTrace, firstCuts, firstClosed⟩ :=
      weightedCoverStep_spec edges weight cuts positive Vfirst initial bounded
    obtain ⟨more, finalCap, restTrace, restCuts, restClosed⟩ :=
      ih (fun batch hb => valid batch (List.mem_cons_of_mem _ hb)) _ cap
    simp only [weightedCoverRun]
    refine ⟨raise.trans more, finalCap, firstTrace.append restTrace, ?_, ?_⟩
    · intro cut member
      rcases List.mem_append.mp member with before | after
      · exact ⟨cuts, List.mem_cons_self, firstCuts cut before⟩
      · obtain ⟨batch, hbatch, hcut⟩ := restCuts cut after
        exact ⟨batch, List.mem_cons_of_mem _ hbatch, hcut⟩
    · intro batch member cut hcut
      rcases List.mem_cons.mp member with rfl | later
      · apply (firstClosed cut hcut).trans
        exact sum_le_sum fun e he => weightedCapacity_mono (positive e ((Vfirst cut hcut).1 he)) (more e)
      · exact restClosed batch later cut hcut

omit [DecidableEq E] in
theorem weightedObjective_eq_capacity_sum (edges : Finset E) (weight charges : E → ℕ)
    (positive : ∀ e ∈ edges, 0 < weight e) (scale : ℕ) :
    (weightedObjective edges weight charges : ℚ) / (scale : ℚ) =
      ∑ e ∈ edges, (weight e : ℚ) * (weightedCapacity (weight e) (charges e) / (scale : ℚ)) := by
  simp only [weightedObjective, Nat.cast_sum, Finset.sum_div]
  apply sum_congr rfl
  intro e he
  unfold weightedCapacity
  have nonzero : (weight e : ℚ) ≠ 0 := (Nat.cast_pos.mpr (positive e he)).ne'
  rw [← mul_div_assoc, mul_div_cancel₀ _ nonzero]

/-- The run covers every revealed cut. Its number of updates and weighted
fractional cost are bounded against any fixed set that hits all these cuts. -/
theorem weightedCoverRun_bound (edges chosen : Finset E) (weight : E → ℕ)
    (batches : List (List (Finset E))) (positive : ∀ e ∈ edges, 0 < weight e)
    (valid : ∀ cuts ∈ batches, ∀ cut ∈ cuts, cut ⊆ edges ∧ cut.Nonempty)
    (chosenSub : chosen ⊆ edges) (hit : ∀ cuts ∈ batches, ∀ cut ∈ cuts, (chosen ∩ cut).Nonempty) :
    let scale := weightedCoverScale edges weight
    let out := weightedCoverRun edges weight batches (fun _ => 0)
    (∀ cuts ∈ batches, ∀ cut ∈ cuts, (scale : ℚ) ≤ weightedCutSum cut weight out.1) ∧
      out.2.length ≤ (scale.log2 + 1) * (∑ e ∈ chosen, weight e) ∧
      (∑ e ∈ edges, (weight e : ℚ) * (weightedCapacity (weight e) (out.1 e) / (scale : ℚ))) ≤
        1 + ((scale.log2 + 1 : ℕ) : ℚ) * (∑ e ∈ chosen, (weight e : ℚ)) := by
  let scale := weightedCoverScale edges weight
  let out := weightedCoverRun edges weight batches (fun _ => 0)
  obtain ⟨_, _, trace, selected, closed⟩ := weightedCoverRun_spec edges weight batches positive valid
    (fun _ => 0) (fun _ _ => Nat.zero_le _)
  have sub : ∀ cut ∈ out.2, cut ⊆ edges := by
    intro cut hc
    obtain ⟨batch, hb, hcut⟩ := selected cut hc
    exact (valid batch hb cut hcut).1
  have touches : ∀ cut ∈ out.2, (chosen ∩ cut).Nonempty := by
    intro cut hc
    obtain ⟨batch, hb, hcut⟩ := selected cut hc
    exact hit batch hb cut hcut
  obtain ⟨updates, objective⟩ := trace.competitive edges chosen chosenSub positive sub touches
  rw [weightedObjective_eq_capacity_sum edges weight _ positive] at objective
  exact ⟨closed, updates, objective⟩

end Updates

end OnlineReachabilityPreservers
