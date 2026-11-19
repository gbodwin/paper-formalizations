import OnlineReachabilityPreservers.SteinerCutFlow
import OnlineReachabilityPreservers.SteinerRoundedCapacities

/-! Online weighted fractional network coverage with request-local free arcs. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Each request has its own free attachments. These arcs are used for its
flow certificate and do not carry over to a different request. -/
structure WeightedNetworkDemand (V : Type*) where
  free : Arcs V
  source : V
  sink : V

variable {V : Type*} [LinearOrder V] [Fintype V]

def weightedNetworkCapacity (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight charges : V × V → ℕ) (scale : ℕ) : ArcFlow V :=
  fun e => if e ∈ d.free then scale else
    if e ∈ edges then roundedWeightedCapacity (weight e) (charges e) else 0

omit [Fintype V] in
theorem weightedNetworkCapacity_nonneg (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight charges : V × V → ℕ) (scale : ℕ) (e : V × V) :
    0 ≤ weightedNetworkCapacity edges d weight charges scale e := by
  unfold weightedNetworkCapacity
  split
  · positivity
  · split <;> positivity

omit [Fintype V] in
theorem weightedNetworkCapacity_mono (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ) (scale : ℕ) (positive : ∀ e ∈ edges, 0 < weight e) :
    Monotone (fun charges => weightedNetworkCapacity edges d weight charges scale) := by
  intro left right order e
  simp only [weightedNetworkCapacity]
  split
  · exact le_rfl
  · split
    · rename_i inside
      exact_mod_cast roundedWeightedCapacity_mono (positive e inside) (order e)
    · exact le_rfl

/-- Full demand flow in the capacitated graph of this particular request. -/
def weightedNetworkCovered (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight charges : V × V → ℕ) (scale : ℕ) : Prop :=
  ∃ f, ValidArcFlow (weightedNetworkCapacity edges d weight charges scale) d.source d.sink scale f

theorem weightedNetworkCovered_mono {edges : Arcs V} {d : WeightedNetworkDemand V}
    {weight left right : V × V → ℕ} {scale : ℕ} (positive : ∀ e ∈ edges, 0 < weight e)
    (order : left ≤ right) (covered : weightedNetworkCovered edges d weight left scale) :
    weightedNetworkCovered edges d weight right scale := by
  obtain ⟨f, valid⟩ := covered
  exact ⟨f, valid.skew,
    fun e => (valid.upper e).trans (weightedNetworkCapacity_mono edges d weight scale positive order e),
    valid.balance⟩

private theorem cutArcFlow_eq_product (f : ArcFlow V) (W : Finset V) :
    cutArcFlow f W = ∑ e ∈ W ×ˢ Wᶜ, f e := by
  rw [cutArcFlow, ← Finset.sum_product']

private theorem no_free_crossing_of_low_capacity {edges : Arcs V} {d : WeightedNetworkDemand V}
    {weight charges : V × V → ℕ} {scale : ℕ} {W : Finset V}
    (small : cutArcFlow (weightedNetworkCapacity edges d weight charges scale) W < (scale : ℤ)) :
    outgoingCut d.free W = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨free, start, finish⟩ := mem_filter.mp he
  have present : e ∈ W ×ˢ Wᶜ := mem_product.mpr ⟨start, mem_compl.mpr finish⟩
  have bound := single_le_sum (f := weightedNetworkCapacity edges d weight charges scale)
    (fun a _ => weightedNetworkCapacity_nonneg edges d weight charges scale a) present
  rw [← cutArcFlow_eq_product] at bound
  have cap : weightedNetworkCapacity edges d weight charges scale e = (scale : ℤ) := by
    simp [weightedNetworkCapacity, free]
  rw [cap] at bound
  exact small.not_ge bound

private theorem weightedNetworkCapacity_cut {edges : Arcs V} {d : WeightedNetworkDemand V}
    (weight charges : V × V → ℕ) (scale : ℕ) (W : Finset V) (noFree : outgoingCut d.free W = ∅) :
    cutArcFlow (weightedNetworkCapacity edges d weight charges scale) W =
      (((∑ e ∈ outgoingCut edges W, roundedWeightedCapacity (weight e) (charges e)) : ℕ) : ℤ) := by
  have capacity (e : V × V) (present : e ∈ W ×ˢ Wᶜ) :
      weightedNetworkCapacity edges d weight charges scale e =
        if e ∈ edges then (roundedWeightedCapacity (weight e) (charges e) : ℤ) else 0 := by
    have notFree : e ∉ d.free := by
      intro free
      obtain ⟨first, last⟩ := mem_product.mp present
      have cross : e ∈ outgoingCut d.free W := mem_filter.mpr ⟨free, first, mem_compl.mp last⟩
      rw [noFree] at cross
      exact notMem_empty e cross
    simp [weightedNetworkCapacity, notFree]
  rw [cutArcFlow_eq_product, sum_congr rfl capacity, ← sum_filter]
  have chosen : (W ×ˢ Wᶜ).filter (fun e => e ∈ edges) = outgoingCut edges W := by
    ext e
    simp [mem_product, mem_compl, outgoingCut, and_assoc, and_comm]
  rw [chosen, Nat.cast_sum]

/-- A positively priced cut returned by the integer flow separator. -/
def weightedNetworkViolation (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ) (scale : ℕ) (charges : V × V → ℕ) : Option (Arcs V) :=
  (findLowCapacityCut (weightedNetworkCapacity edges d weight charges scale) d.source d.sink scale).map
    (outgoingCut edges)

theorem weightedNetworkViolation_some {edges : Arcs V} {d : WeightedNetworkDemand V}
    {weight charges : V × V → ℕ} {scale : ℕ} {C : Arcs V} (positive : ∀ e ∈ edges, 0 < weight e)
    (answer : weightedNetworkViolation edges d weight scale charges = some C) :
    weightedCutSum C weight charges < (scale : ℚ) ∧
      ∃ W : Finset V, d.source ∈ W ∧ d.sink ∉ W ∧ outgoingCut d.free W = ∅ ∧
        C = outgoingCut edges W := by
  let cap := weightedNetworkCapacity edges d weight charges scale
  have check := findLowCapacityCut_spec cap d.source d.sink scale
    (weightedNetworkCapacity_nonneg edges d weight charges scale)
  cases h : findLowCapacityCut cap d.source d.sink scale with
  | none => simp [weightedNetworkViolation, cap, h] at answer
  | some W =>
    rw [h] at check
    have eq : C = outgoingCut edges W := by simpa [weightedNetworkViolation, cap, h] using answer.symm
    obtain ⟨source, sink, below⟩ := check
    have noFree := no_free_crossing_of_low_capacity below
    rw [weightedNetworkCapacity_cut weight charges scale W noFree] at below
    refine ⟨?_, W, source, sink, noFree, eq⟩
    rw [eq]
    exact (weightedCutSum_le_rounded _ _ _ (fun e he => positive e (mem_filter.mp he).1)).trans_lt
      (by exact_mod_cast below)

theorem weightedNetworkViolation_none {edges : Arcs V} {d : WeightedNetworkDemand V}
    {weight charges : V × V → ℕ} {scale : ℕ} (answer : weightedNetworkViolation edges d weight scale charges = none) :
    weightedNetworkCovered edges d weight charges scale := by
  let cap := weightedNetworkCapacity edges d weight charges scale
  have h : findLowCapacityCut cap d.source d.sink scale = none := by
    simpa [weightedNetworkViolation, cap] using answer
  have check := findLowCapacityCut_spec cap d.source d.sink scale
    (weightedNetworkCapacity_nonneg edges d weight charges scale)
  rw [h] at check
  exact ⟨_, check⟩

omit [LinearOrder V] [Fintype V] in
private theorem reach_crosses_cut {G : Arcs V} {s t : V} (reach : Reach G s t)
    (W : Finset V) (start : s ∈ W) (finish : t ∉ W) :
    ∃ e ∈ G, e.1 ∈ W ∧ e.2 ∉ W := by
  classical
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl => exact (finish start).elim
  | @head source next edge rest ih =>
    by_cases member : next ∈ W
    · exact ih member
    · exact ⟨(source, next), edge, start, member⟩

private def networkCut (edges : Arcs V) (d : WeightedNetworkDemand V) (cut : Arcs V) : Prop :=
  ∃ W : Finset V, d.source ∈ W ∧ d.sink ∉ W ∧ outgoingCut d.free W = ∅ ∧
    cut = outgoingCut edges W

omit [Fintype V] in
private theorem networkCut_sub {edges : Arcs V} {d : WeightedNetworkDemand V} {cut : Arcs V}
    (valid : networkCut edges d cut) : cut ⊆ edges := by
  obtain ⟨W, _, _, _, rfl⟩ := valid
  exact filter_subset _ _

omit [Fintype V] in
private theorem networkCut_hit {edges chosen : Arcs V} {d : WeightedNetworkDemand V} {cut : Arcs V}
    (sub : chosen ⊆ edges) (reach : Reach (chosen ∪ d.free) d.source d.sink)
    (valid : networkCut edges d cut) : (chosen ∩ cut).Nonempty := by
  obtain ⟨W, source, sink, none, rfl⟩ := valid
  obtain ⟨e, mem, e₁, e₂⟩ := reach_crosses_cut reach W source sink
  rcases mem_union.mp mem with inChosen | free
  · exact ⟨e, mem_inter.mpr ⟨inChosen, mem_filter.mpr ⟨sub inChosen, e₁, e₂⟩⟩⟩
  · have he : e ∈ outgoingCut d.free W := mem_filter.mpr ⟨free, e₁, e₂⟩
    rw [none] at he
    exact (notMem_empty e he).elim

def weightedNetworkStep (edges : Arcs V) (weight : V × V → ℕ) (d : WeightedNetworkDemand V)
    (initial : V × V → ℕ) : (V × V → ℕ) × List (Arcs V) :=
  weightedCoverLoop (weightedNetworkViolation edges d weight (weightedCoverScale edges weight))
    (weightedCoverFuel edges weight) initial

/-- The update runs the flow separator on the rounded capacities and
preserves all charge bounds. -/
theorem weightedNetworkStep_spec (edges : Arcs V) (weight : V × V → ℕ) (d : WeightedNetworkDemand V)
    (positive : ∀ e ∈ edges, 0 < weight e) (reachable : Reach (edges ∪ d.free) d.source d.sink)
    (initial : V × V → ℕ)
    (bounded : ∀ e ∈ edges, initial e ≤ ((weightedCoverScale edges weight).log2 + 1) * weight e) :
    let scale := weightedCoverScale edges weight
    let out := weightedNetworkStep edges weight d initial
    initial ≤ out.1 ∧ (∀ e ∈ edges, out.1 e ≤ (scale.log2 + 1) * weight e) ∧
      WeightedCutUpdates weight scale initial out.2 out.1 ∧
      (∀ cut ∈ out.2, networkCut edges d cut) ∧ weightedNetworkCovered edges d weight out.1 scale := by
  let scale := weightedCoverScale edges weight
  let out := weightedNetworkStep edges weight d initial
  have scalePos : 0 < scale := zero_lt_one.trans_le (le_max_left _ _)
  have sound {charges C} (answer : weightedNetworkViolation edges d weight scale charges = some C) :
      networkCut edges d C ∧ weightedCutSum C weight charges < (scale : ℚ) :=
    (weightedNetworkViolation_some positive answer).symm
  have complete {charges} (answer : weightedNetworkViolation edges d weight scale charges = none) :
      weightedNetworkCovered edges d weight charges scale := weightedNetworkViolation_none answer
  obtain ⟨trace, cuts, done⟩ := weightedCoverLoop_certify weight scale _ (networkCut edges d)
    (fun charges => weightedNetworkCovered edges d weight charges scale) sound complete
    (weightedCoverFuel edges weight) initial
  change WeightedCutUpdates weight scale initial out.2 out.1 at trace
  change ∀ cut ∈ out.2, networkCut edges d cut at cuts
  change out.2.length < weightedCoverFuel edges weight →
    weightedNetworkCovered edges d weight out.1 scale at done
  have inside : ∀ cut ∈ out.2, cut ⊆ edges := fun c hc => networkCut_sub (cuts c hc)
  have touches : ∀ cut ∈ out.2, (edges ∩ cut).Nonempty :=
    fun c hc => networkCut_hit Subset.rfl reachable (cuts c hc)
  obtain ⟨mono, cap, steps, _⟩ := trace.bound edges edges positive scalePos inside touches bounded
  have fuel : out.2.length < weightedCoverFuel edges weight := by
    have upper : ∑ e ∈ edges, out.1 e ≤ (scale.log2 + 1) * (∑ e ∈ edges, weight e) := by
      rw [mul_sum]
      exact sum_le_sum cap
    change out.2.length < (scale.log2 + 1) * (∑ e ∈ edges, weight e) + 1
    omega
  exact ⟨mono, cap, trace, cuts, done fuel⟩

def weightedNetworkRun (edges : Arcs V) (weight : V × V → ℕ) :
    List (WeightedNetworkDemand V) → (V × V → ℕ) → (V × V → ℕ) × List (Arcs V)
  | [], initial => (initial, [])
  | d :: rest, initial =>
    let first := weightedNetworkStep edges weight d initial
    let last := weightedNetworkRun edges weight rest first.1
    (last.1, first.2 ++ last.2)

theorem weightedNetworkRun_spec (edges : Arcs V) (weight : V × V → ℕ)
    (requests : List (WeightedNetworkDemand V))
    (positive : ∀ e ∈ edges, 0 < weight e)
    (reachable : ∀ d ∈ requests, Reach (edges ∪ d.free) d.source d.sink)
    (initial : V × V → ℕ)
    (bounded : ∀ e ∈ edges, initial e ≤ ((weightedCoverScale edges weight).log2 + 1) * weight e) :
    let scale := weightedCoverScale edges weight
    let out := weightedNetworkRun edges weight requests initial
    initial ≤ out.1 ∧ (∀ e ∈ edges, out.1 e ≤ (scale.log2 + 1) * weight e) ∧
      WeightedCutUpdates weight scale initial out.2 out.1 ∧
      (∀ cut ∈ out.2, ∃ d ∈ requests, networkCut edges d cut) ∧
      (∀ d ∈ requests, weightedNetworkCovered edges d weight out.1 scale) := by
  induction requests generalizing initial with
  | nil =>
    exact ⟨le_rfl, bounded, .nil _, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | cons d rest ih =>
    obtain ⟨raise, cap, firstTrace, firstCut, firstCovered⟩ :=
      weightedNetworkStep_spec edges weight d positive (reachable d List.mem_cons_self) initial bounded
    obtain ⟨more, finalCap, restTrace, restCut, restCovered⟩ :=
      ih (fun a ha => reachable a (List.mem_cons_of_mem _ ha)) _ cap
    simp only [weightedNetworkRun]
    refine ⟨raise.trans more, finalCap, firstTrace.append restTrace, ?_, ?_⟩
    · intro cut member
      rcases List.mem_append.mp member with comesFirst | comesLater
      · exact ⟨d, List.mem_cons_self, firstCut cut comesFirst⟩
      · obtain ⟨a, ha, certified⟩ := restCut cut comesLater
        exact ⟨a, List.mem_cons_of_mem _ ha, certified⟩
    · intro a member
      rcases List.mem_cons.mp member with rfl | ha
      · exact weightedNetworkCovered_mono positive more firstCovered
      · exact restCovered a ha

/-- A competitive fractional network run with actual cut separation. The
certificate for each demand uses only its own free attachments. -/
theorem weightedNetworkRun_bound (edges chosen : Arcs V) (weight : V × V → ℕ)
    (requests : List (WeightedNetworkDemand V)) (positive : ∀ e ∈ edges, 0 < weight e)
    (sub : chosen ⊆ edges) (all : ∀ d ∈ requests, Reach (chosen ∪ d.free) d.source d.sink) :
    let scale := weightedCoverScale edges weight
    let out := weightedNetworkRun edges weight requests (fun _ => 0)
    (∀ d ∈ requests, weightedNetworkCovered edges d weight out.1 scale) ∧
      out.2.length ≤ (scale.log2 + 1) * (∑ e ∈ chosen, weight e) ∧
      (∑ e ∈ edges, (weight e : ℚ) * ((roundedWeightedCapacity (weight e) (out.1 e) : ℚ) / scale)) ≤
        2 + ((scale.log2 + 1 : ℕ) : ℚ) * (∑ e ∈ chosen, (weight e : ℚ)) := by
  let scale := weightedCoverScale edges weight
  let out := weightedNetworkRun edges weight requests (fun _ => 0)
  have reach (d) (member : d ∈ requests) : Reach (edges ∪ d.free) d.source d.sink :=
    reach_mono (Finset.union_subset_union_left sub) (all d member)
  obtain ⟨_, _, trace, selection, covered⟩ := weightedNetworkRun_spec edges weight requests positive
    reach (fun _ => 0) (fun _ _ => Nat.zero_le _)
  have cutsSub : ∀ cut ∈ out.2, cut ⊆ edges := by
    intro cut hc
    obtain ⟨d, _, h⟩ := selection cut hc
    exact networkCut_sub h
  have touch : ∀ cut ∈ out.2, (chosen ∩ cut).Nonempty := by
    intro cut hc
    obtain ⟨d, hd, h⟩ := selection cut hc
    exact networkCut_hit sub (all d hd) h
  obtain ⟨count, cost⟩ := trace.competitive edges chosen sub positive cutsSub touch
  refine ⟨covered, count, ?_⟩
  have rounded := roundedWeightedObjective_le edges weight out.1 positive
  change (weightedObjective edges weight out.1 : ℚ) / (scale : ℚ) ≤
    1 + ((scale.log2 + 1 : ℕ) : ℚ) * (∑ e ∈ chosen, (weight e : ℚ)) at cost
  exact rounded.trans (by linarith only [cost])

end OnlineReachabilityPreservers
