import OnlineReachabilityPreservers.SteinerBitMeasure

/-! A fixed supply of fair bits preserves the competitive rate with a fallback. -/

namespace OnlineReachabilityPreservers

universe u

open MeasureTheory
open scoped ENNReal

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- A fixed fair-bit budget sufficient to bound the expected fallback cost by one edge. -/
def steinerBitBudget (G : Arcs V) (height : ℕ) : ℕ :=
  completeSteinerSeedBitBound G height * G.card

theorem steinerBitBudget_polynomial (G : Arcs V) (height : ℕ) :
    steinerBitBudget G height ≤ completeSteinerSeedPolynomial (Fintype.card V) G.card height * G.card :=
  Nat.mul_le_mul_right _ (completeSteinerSeedBitBound_polynomial G height)

private def decodeBudgetSeed (G : Arcs V) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool) :=
  decodeCompleteSteinerSeed G height (steinerEarlyCoordinateIndex G height) (steinerVertexIndex V)
    (steinerArcIndex G) (List.ofFn bits)

private def steinerBudgetFallback (G : Arcs V) (D : List (V × V)) : Arcs V :=
  if distinctNonselfTrace D = [] then ∅ else G

private theorem scanl_or_eq_prefix_any {A : Type*} (predicate : A → Bool)
    (arrivals : List A) (seen : Bool) :
    arrivals.scanl (fun seen x => seen || predicate x) seen =
      arrivals.inits.map (fun P => seen || P.any predicate) := by
  induction arrivals generalizing seen with
  | nil => simp [List.scanl_nil]
  | cons first rest ih =>
    simp [List.scanl_cons, ih, List.map_map, Function.comp_def, Bool.or_assoc]

omit [Fintype V] in
private theorem distinctNonselfTrace_eq_nil_of_all_self {D : List (V × V)} :
    distinctNonselfTrace D = [] ↔ ∀ d ∈ D, d.1 = d.2 := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro none d present
    by_contra different
    exact none d (mem_distinctNonselfTrace.mpr ⟨present,different⟩)
  · intro same d member
    obtain ⟨present,different⟩ := mem_distinctNonselfTrace.mp member
    exact different (same d present)

/-- The exhausted-word branch can replay its purchases with one Boolean state. -/
def steinerFallbackPrefixScan (G : Arcs V) (D : List (V × V)) : List (Arcs V × ℕ) :=
  (D.scanl (fun seen d => seen || decide (d.1 ≠ d.2)) false).map
    (fun seen => (if seen then G else ∅, 0))

omit [Fintype V] in
theorem steinerFallbackPrefixScan_eq (G : Arcs V) (D : List (V × V)) :
    steinerFallbackPrefixScan G D =
      D.inits.map (fun P => (if distinctNonselfTrace P = [] then ∅ else G, 0)) := by
  unfold steinerFallbackPrefixScan
  rw [scanl_or_eq_prefix_any, List.map_map]
  apply List.map_congr_left
  intro P _
  simp only [Function.comp_apply, Bool.false_or]
  have empty : P.any (fun d => decide (d.1 ≠ d.2)) = false ↔ distinctNonselfTrace P = [] := by
    rw [List.any_eq_false, distinctNonselfTrace_eq_nil_of_all_self]
    simp
  cases result : P.any (fun d => decide (d.1 ≠ d.2)) with
  | false => simp [empty.mp result]
  | true =>
    have nonempty : distinctNonselfTrace P ≠ [] := fun h => by
      have contradiction := empty.mpr h
      rw [result] at contradiction
      cases contradiction
    simp [nonempty]

private theorem steinerDrawRun_eq_empty (G : Arcs V) (height : ℕ)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V)
    (thin : ThinSample G) (D : List (V × V)) (empty : distinctNonselfTrace D = []) :
    completeSteinerDrawRun G height early hubs thin D = ∅ := by
  simp [completeSteinerDrawRun, completeSteinerRun, empty, earlyRoundedGraph_empty, assembledSteiner_empty]

/-- On an exhausted seed prefix, buy the input graph at the first non-self request. -/
def completeSteinerRunWithBitBudget (G : Arcs V) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) : Arcs V :=
  match decodeBudgetSeed G height bits with
  | none => steinerBudgetFallback G D
  | some result => completeSteinerDrawRun G height result.1.1 result.1.2.1 result.1.2.2 D

theorem completeSteinerRunWithBitBudget_correct (G : Arcs V) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    completeSteinerRunWithBitBudget G height bits D ⊆ G ∧
    Preserves G (completeSteinerRunWithBitBudget G height bits D) D := by
  cases read : decodeBudgetSeed G height bits with
  | none =>
    simp only [completeSteinerRunWithBitBudget, read, steinerBudgetFallback]
    split
    · rename_i empty
      refine ⟨Finset.empty_subset _, fun d hd => ?_⟩
      have eq : d.1 = d.2 := by
        by_contra different
        have member := mem_distinctNonselfTrace.mpr ⟨hd,different⟩
        simp [empty] at member
      rw [eq]
      exact ⟨fun _ => Relation.ReflTransGen.refl, fun _ => Relation.ReflTransGen.refl⟩
    · exact ⟨fun _ member => member, fun _ _ => Iff.rfl⟩
  | some seed =>
    simpa only [completeSteinerRunWithBitBudget, read] using
      completeSteinerDrawRun_correct G height seed.1.1 seed.1.2.1 seed.1.2.2 D feasible

theorem completeSteinerRunWithBitBudget_prefix (G : Arcs V) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) {D E : List (V × V)}
    (prefixOf : D <+: E) (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    completeSteinerRunWithBitBudget G height bits D ⊆ completeSteinerRunWithBitBudget G height bits E := by
  cases read : decodeBudgetSeed G height bits with
  | none =>
    simp only [completeSteinerRunWithBitBudget, read, steinerBudgetFallback]
    by_cases empty : distinctNonselfTrace D = []
    · simp [empty]
    · have later : distinctNonselfTrace E ≠ [] := by
        intro eq
        have pref := distinctNonselfTrace_prefix prefixOf
        rw [eq, List.prefix_nil] at pref
        exact empty pref
      simp [empty, later]
  | some seed =>
    simpa only [completeSteinerRunWithBitBudget, read] using
      completeSteinerDrawRun_prefix G height seed.1.1 seed.1.2.1 seed.1.2.2 prefixOf feasible

/-- Decode the fixed bit word once, then replay every prefix with a shared preparation. -/
def completeSteinerReplayWithBitBudget (G : Arcs V) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) :
    List (Arcs V × ℕ) × ℕ × ℕ × ℕ :=
  match decodeBudgetSeed G height bits with
  | none => (steinerFallbackPrefixScan G D,0,0,0)
  | some seed => completeSteinerPrefixSearchReplayWithWeightWork G height seed.1.1 seed.1.2.1 seed.1.2.2 D

/-- The bounded-bit replay returns the online graphs and keeps the existing
polynomial bound on metered operations. The supply of bits is fixed separately. -/
theorem completeSteinerReplayWithBitBudget_spec (G : Arcs V) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeSteinerReplayWithBitBudget G height bits D
    out.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (out.1.map Prod.snd).sum + out.2.1 + out.2.2.1 + out.2.2.2 ≤
        completeSteinerWeightWorkPolynomial (Fintype.card V) G.card height D.length := by
  cases read : decodeBudgetSeed G height bits with
  | none => simp [completeSteinerReplayWithBitBudget, completeSteinerRunWithBitBudget, read,
      steinerFallbackPrefixScan_eq, steinerBudgetFallback, List.map_map, Function.comp_def]
  | some seed =>
    have run : completeSteinerRunWithBitBudget G height bits =
        completeSteinerDrawRun G height seed.1.1 seed.1.2.1 seed.1.2.2 := by
      funext P
      simp only [completeSteinerRunWithBitBudget, read]
    simpa only [completeSteinerReplayWithBitBudget, read, run] using
      completeSteinerPrefixSearchReplayWithWeightWork_polynomial G height seed.1.1 seed.1.2.1 seed.1.2.2 D feasible

private def steinerBudgetFailure (G : Arcs V) (height : ℕ) : Set (ℕ → Bool) :=
  {stream | decodeBudgetSeed G height (fairBitPrefix (steinerBitBudget G height) stream) = none}

private theorem steinerBudgetFailure_measurable (G : Arcs V) (height : ℕ) :
    MeasurableSet (steinerBudgetFailure G height) := by
  let failure : Set (Fin (steinerBitBudget G height) → Bool) := {bits | decodeBudgetSeed G height bits = none}
  exact failure.toFinite.measurableSet.preimage (fairBitPrefix_measurable _)

private theorem steinerBudget_cost_ae (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    ∀ᵐ stream ∂fairBitMeasure,
      ((completeSteinerRunWithBitBudget G height (fairBitPrefix (steinerBitBudget G height) stream) D).card : ℝ≥0∞) ≤
        fairBitDecoderEdgeCount G height (steinerEarlyCoordinateIndex G height) (steinerVertexIndex V)
          (steinerArcIndex G) D stream + (steinerBudgetFailure G height).indicator (fun _ => (G.card : ℝ≥0∞)) stream := by
  filter_upwards [fairBitDecoderEdgeCount_ae_decode_prefix G height
    (steinerEarlyCoordinateIndex G height) (steinerVertexIndex V) (steinerArcIndex G) D] with stream agrees
  let input := fairBitPrefix (steinerBitBudget G height) stream
  cases read : decodeBudgetSeed G height input with
  | none =>
    have failed : stream ∈ steinerBudgetFailure G height := read
    rw [Set.indicator_of_mem failed]
    change (((completeSteinerRunWithBitBudget G height input D).card : ℕ) : ℝ≥0∞) ≤ _
    simp only [completeSteinerRunWithBitBudget, read, steinerBudgetFallback]
    split
    · simp
    · exact le_add_self
  | some parsed =>
    obtain ⟨seed, counts, rest⟩ := parsed
    rw [agrees _ seed counts rest read]
    change (((completeSteinerRunWithBitBudget G height input D).card : ℕ) : ℝ≥0∞) ≤ _
    simp only [completeSteinerRunWithBitBudget, read]
    exact le_self_add

private theorem steinerBudget_failureCharge_le_one (G : Arcs V) (height : ℕ) :
    (G.card : ℝ≥0∞) * fairBitMeasure (steinerBudgetFailure G height) ≤ 1 := by
  let B := completeSteinerSeedBitBound G height
  let budget := steinerBitBudget G height
  have fail : fairBitMeasure (steinerBudgetFailure G height) ≤ (B : ℝ≥0∞) / (budget+1 : ℕ) :=
    (fairBitDecoder_failure_le_expected G height (steinerEarlyCoordinateIndex G height) (steinerVertexIndex V)
      (steinerArcIndex G) budget).trans (by
        refine ENNReal.div_le_div_right ?_ _
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (completeSteinerExpectedSeedBits_le_bound G height))
  calc
    _ ≤ (G.card : ℝ≥0∞) * ((B : ℝ≥0∞) / (budget+1 : ℕ)) := by gcongr
    _ = (budget : ℝ≥0∞) / (budget+1 : ℕ) := by
      rw [← mul_div_assoc, ← Nat.cast_mul, Nat.mul_comm]
      rfl
    _ ≤ 1 := ENNReal.div_le_of_le_mul (by simp)

/-- A single fixed prefix of polynomial length incurs at most one extra edge in expectation. -/
theorem steinerBudget_expected_le (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    (∫⁻ stream, ((completeSteinerRunWithBitBudget G height (fairBitPrefix (steinerBitBudget G height) stream) D).card : ℝ≥0∞)
      ∂fairBitMeasure) ≤ ENNReal.ofReal (completeSteinerMean G height D) + 1 := by
  let edge := fairBitDecoderEdgeCount G height (steinerEarlyCoordinateIndex G height)
    (steinerVertexIndex V) (steinerArcIndex G) D
  let extra := (steinerBudgetFailure G height).indicator (fun _ => (G.card : ℝ≥0∞))
  have measurable : Measurable extra := measurable_const.indicator (steinerBudgetFailure_measurable G height)
  calc
    _ ≤ ∫⁻ stream, edge stream + extra stream ∂fairBitMeasure := lintegral_mono_ae (steinerBudget_cost_ae G height D)
    _ = (∫⁻ stream, edge stream ∂fairBitMeasure) + ∫⁻ stream, extra stream ∂fairBitMeasure := by
      simp only [add_comm (edge _) (extra _)]
      rw [lintegral_add_left measurable, add_comm]
    _ = ENNReal.ofReal (completeSteinerMean G height D) + (G.card : ℝ≥0∞) * fairBitMeasure (steinerBudgetFailure G height) := by
      unfold edge extra
      rw [fairBitDecoderEdgeIntegral_eq, lintegral_indicator_const (steinerBudgetFailure_measurable G height)]
    _ ≤ _ := add_le_add_right (steinerBudget_failureCharge_le_one G height) _

/-- Theorems 8 and 21 with a fixed polynomial fair-bit budget, retaining the same competitive exponent. -/
theorem theorem21_online_steiner_bounded_bits {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (W : Type u) [LinearOrder W] [Fintype W] {G Z : Arcs W}
        (D : List (W × W)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, ((completeSteinerRunWithBitBudget G height (fairBitPrefix (steinerBitBudget G height) stream) D).card : ℝ≥0∞)
          ∂fairBitMeasure) ≤ ENNReal.ofReal (K * (Fintype.card W : ℝ) ^ (3/5 + ε) * Z.card) := by
  obtain ⟨height, heightPos, K, Kpos, rate⟩ := theorem21_online_steiner_expected.{u} epsilon
  refine ⟨height,heightPos,K+1,by positivity,?_⟩
  intro W _ _ G Z D sub feasible
  by_cases noEdges : Z = ∅
  · have empty : distinctNonselfTrace D = [] := by
      cases distinct : distinctNonselfTrace D with
      | nil => rfl
      | cons request rest =>
        have member : request ∈ distinctNonselfTrace D := by rw [distinct]; exact List.mem_cons_self
        obtain ⟨inTrace, different⟩ := mem_distinctNonselfTrace.mp member
        have path : Reach (∅ : Arcs W) request.1 request.2 := noEdges ▸ feasible request inTrace
        have onlySelf {s t : W} (p : Reach (∅ : Arcs W) s t) : s = t := by
          cases p with
          | refl => rfl
          | tail _ edge => exact (Finset.notMem_empty _ edge).elim
        exact (different (onlySelf path)).elim
    have zero (bits : Fin (steinerBitBudget G height) → Bool) :
        completeSteinerRunWithBitBudget G height bits D = ∅ := by
      cases read : decodeBudgetSeed G height bits with
      | none => simp [completeSteinerRunWithBitBudget, read, steinerBudgetFallback, empty]
      | some seed =>
        simpa only [completeSteinerRunWithBitBudget, read] using
          steinerDrawRun_eq_empty G height seed.1.1 seed.1.2.1 seed.1.2.2 D empty
    simp [zero]
  · have positive : 0 < Z.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr noEdges)
    obtain ⟨edge, _⟩ := Finset.card_pos.mp positive
    have vertices : (1 : ℝ) ≤ Fintype.card W := by exact_mod_cast (@Fintype.card_pos W _ ⟨edge.1⟩)
    have comparator : (1 : ℝ) ≤ Z.card := by exact_mod_cast positive
    let value := (Fintype.card W : ℝ) ^ (3/5 + ε) * Z.card
    have large : 1 ≤ value := one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow vertices (by linarith)) comparator
    have original := rate W D sub feasible
    have scale : K * (Fintype.card W : ℝ) ^ (3/5 + ε) * Z.card + 1 ≤
        (K+1) * (Fintype.card W : ℝ) ^ (3/5 + ε) * Z.card := by
      calc
        _ ≤ K * (Fintype.card W : ℝ) ^ (3/5 + ε) * Z.card + value := add_le_add le_rfl large
        _ = _ := by dsimp [value]; ring
    refine (steinerBudget_expected_le G height D).trans ((add_le_add (ENNReal.ofReal_le_ofReal original) le_rfl).trans ?_)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num)]
    exact ENNReal.ofReal_le_ofReal scale

/-- Expected competitive cost for one uniformly chosen fixed-length bit string. -/
theorem theorem21_online_steiner_bounded_bits_finite {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (W : Type u) [LinearOrder W] [Fintype W] {G Z : Arcs W}
        (D : List (W × W)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∑ bits : Fin (steinerBitBudget G height) → Bool,
          ((completeSteinerRunWithBitBudget G height bits D).card : ℝ)) /
          (Fintype.card (Fin (steinerBitBudget G height) → Bool) : ℝ) ≤
          K * (Fintype.card W : ℝ) ^ (3/5 + ε) * Z.card := by
  obtain ⟨height,heightPos,K,Kpos,bound⟩ := theorem21_online_steiner_bounded_bits.{u} epsilon
  refine ⟨height,heightPos,K,Kpos,?_⟩
  intro W _ _ G Z D sub feasible
  have law := bound W D sub feasible
  rw [fairBitPrefix_lintegral_eq (steinerBitBudget G height)
    (fun bits => (completeSteinerRunWithBitBudget G height bits D).card)] at law
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp law

private theorem boundedBitWord_cast {a b : ℕ} (width : a = b) (bits : Fin b → Bool) :
    List.ofFn (fun i : Fin a => bits (Fin.cast width i)) = List.ofFn bits := by
  subst a
  rfl

/-- Compute and share the forest scale for the bit count, the decoder, and replay. -/
def completeSteinerReplayWithCachedBitBudget (G : Arcs V) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) :
    List (Arcs V × ℕ) × ℕ × ℕ × ℕ :=
  let prepared := prepareEarlyDistanceTableForSeed G height
  let width := prepared.1.val.log2+1
  let widthEq := congrArg (fun scale : ℕ => scale.log2+1) prepared.1.property
  let vertices := steinerUniverseArrayIndex V
  let coordinates := steinerEarlyCoordinateIndexAtWidth G height width widthEq vertices
  let arcs := steinerArcArrayIndex G
  let budget := completeSteinerSeedBitBoundAtWidth G height width * G.card
  let budgetEq : budget = steinerBitBudget G height :=
    congrArg (· * G.card) (completeSteinerSeedBitBoundAtWidth_eq G height width widthEq)
  let raw := List.ofFn (fun i : Fin budget => bits (Fin.cast budgetEq i))
  let result := decodeCompleteSteinerSeedAtWidth G height width widthEq coordinates vertices arcs raw
  let rounds := match result with
    | none => steinerFallbackPrefixScan G D
    | some seed => D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G
        (prepared.2.1 seed.1.1) seed.1.2.1 seed.1.2.2)
  (rounds,prepared.2.2)

private theorem prepareSteinerSeed_work_polynomial (G : Arcs V) (height p : ℕ) :
    let work := (prepareEarlyDistanceTableForSeed G height).2.2
    work.1 + work.2.1 + work.2.2 ≤ completeSteinerWeightWorkPolynomial (Fintype.card V) G.card height p := by
  let n := Fintype.card V
  let H := (height+1)*n^height
  let F := (n*2)*H
  let work := (prepareEarlyDistanceTableForSeed G height).2.2
  obtain ⟨table, template, weights⟩ := prepareEarlyDistanceTableForSeed_work_le G height
  have forest : Fintype.card (HeightForestVertex V height) ≤ F := by
    cases isEmpty_or_nonempty V with
    | inl empty => simp [HeightForestVertex]
    | inr ne => exact heightForestVertex_card_le V height
  have templateCap : work.2.1 ≤ n*(2*H*height*n^2) := by
    apply template.trans
    change n*(2*Fintype.card (HeightNode V height)*height*n^2) ≤ n*(2*H*height*n^2)
    cases isEmpty_or_nonempty V with
    | inl empty => simp [n]
    | inr ne =>
      have histories : Fintype.card (HeightNode V height) ≤ H := heightNode_card_le V height
      gcongr
  have weightCap : work.2.2 ≤ F^2*n^2 :=
    weights.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left forest _))
  have base : work.1 + work.2.1 + work.2.2 ≤ n^2*((n+1)*n*G.card) + n*(2*H*height*n^2) + F^2*n^2 :=
    Nat.add_le_add (Nat.add_le_add table templateCap) weightCap
  refine base.trans ?_
  unfold completeSteinerWeightWorkPolynomial
  dsimp only [n,H,F]
  omega

/-- The shared preparation preserves the bounded-bit graphs and accounts for
its own measured work even when the seed is exhausted. -/
theorem completeSteinerReplayWithCachedBitBudget_spec (G : Arcs V) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeSteinerReplayWithCachedBitBudget G height bits D
    out.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (out.1.map Prod.snd).sum + out.2.1 + out.2.2.1 + out.2.2.2 ≤
        completeSteinerWeightWorkPolynomial (Fintype.card V) G.card height D.length := by
  let prepared := prepareEarlyDistanceTableForSeed G height
  let width := prepared.1.val.log2+1
  let widthEq := congrArg (fun scale : ℕ => scale.log2+1) prepared.1.property
  let budget := completeSteinerSeedBitBoundAtWidth G height width * G.card
  let budgetEq : budget = steinerBitBudget G height :=
    congrArg (· * G.card) (completeSteinerSeedBitBoundAtWidth_eq G height width widthEq)
  have rawEq := boundedBitWord_cast budgetEq bits
  have readEq : decodeCompleteSteinerSeed G height (steinerEarlyCoordinateIndex G height)
      (steinerVertexIndex V) (steinerArcIndex G) (List.ofFn (fun i : Fin budget => bits (Fin.cast budgetEq i))) =
        decodeBudgetSeed G height bits := by rw [rawEq, decodeBudgetSeed]
  simp only [completeSteinerReplayWithCachedBitBudget, decodeCompleteSteinerSeedAtWidth_eq,
    steinerUniverseArrayIndex_eq, steinerArcArrayIndex_eq, steinerEarlyCoordinateIndexAtWidth_eq]
  erw [readEq]
  cases read : decodeBudgetSeed G height bits with
  | none =>
    simpa [completeSteinerRunWithBitBudget, read, steinerFallbackPrefixScan_eq,
      steinerBudgetFallback, List.map_map, Function.comp_def] using
      prepareSteinerSeed_work_polynomial G height D.length
  | some seed =>
    have run : completeSteinerRunWithBitBudget G height bits =
        completeSteinerDrawRun G height seed.1.1 seed.1.2.1 seed.1.2.2 := by
      funext P
      simp only [completeSteinerRunWithBitBudget, read]
    simpa only [run, completeSteinerPrefixSearchReplayWithWeightWork,
      prepareEarlyDistanceTableWithWeightWork] using
      completeSteinerPrefixSearchReplayWithWeightWork_polynomial
        G height seed.1.1 seed.1.2.1 seed.1.2.2 D feasible

end OnlineReachabilityPreservers
