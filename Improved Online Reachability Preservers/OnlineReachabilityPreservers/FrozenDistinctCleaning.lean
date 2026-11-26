import OnlineReachabilityPreservers.DistinctPathBudgets
import OnlineReachabilityPreservers.FrozenBoundaryCases
import OnlineReachabilityPreservers.FrozenHalfFourCleaning
import OnlineReachabilityPreservers.HalfGridCleaning

/-! Frozen-average cleaning for the literal simple path set convention. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

/-- The lower path cap forces distinct nonempty rows when the input mean exceeds four. -/
theorem frozen_length_distinct_of_large_mean {n p M v q k : ℕ}
    {paths : Fin q → List (Fin v)} (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (two : 2 ≤ k) (pPos : 0 < p)
    (long : 4*p < M) (caps : frozenListCaps n p M paths) :
    Function.Injective paths ∧ ∀ i, paths i ≠ [] := by
  have minimum : (1:ℝ) < (M:ℝ)/(4*(p:ℝ)) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    have m : (4:ℝ)*(p:ℝ) < M := by exact_mod_cast long
    simpa using m
  have length (i : Fin q) : 2 ≤ (paths i).length := by
    have l := minimum.trans_le (caps.2 i).1
    have k : 1 < (paths i).length := by exact_mod_cast l
    omega
  exact ⟨nontrivial_halfFree_paths_injective simple length two free,
    fun i empty => by simpa [empty] using length i⟩

private def singletonExtendedRows {n q : ℕ} (paths : Fin q → List (Fin n)) :
    Fin (q+n) → List (Fin n) :=
  Fin.addCases paths (fun v => [v])

private theorem singletonExtendedRows_simple {n q : ℕ} {paths : Fin q → List (Fin n)}
    (simple : ∀ i, (paths i).Nodup) (i : Fin (q+n)) : (singletonExtendedRows paths i).Nodup := by
  refine Fin.addCases (motive := fun i => (singletonExtendedRows paths i).Nodup) ?_ ?_ i
  · intro j
    simpa [singletonExtendedRows] using simple j
  · intro v
    simp [singletonExtendedRows]

private theorem singletonExtendedRows_injective {n q : ℕ} {paths : Fin q → List (Fin n)}
    (injective : Function.Injective paths) (long : ∀ i, 2 ≤ (paths i).length) :
    Function.Injective (singletonExtendedRows paths) := by
  intro i
  refine Fin.addCases (motive := fun i => ∀ j, singletonExtendedRows paths i =
    singletonExtendedRows paths j → i = j) ?_ ?_ i
  · intro a j
    refine Fin.addCases (motive := fun j => singletonExtendedRows paths (Fin.castAdd n a) =
      singletonExtendedRows paths j → Fin.castAdd n a = j) ?_ ?_ j
    · intro b eq
      exact congrArg (Fin.castAdd n) (injective (by simpa [singletonExtendedRows] using eq))
    · intro v eq
      have lengths := congrArg List.length eq
      have bound := long a
      simp [singletonExtendedRows] at lengths
      omega
  · intro u j
    refine Fin.addCases (motive := fun j => singletonExtendedRows paths (Fin.natAdd q u) =
      singletonExtendedRows paths j → Fin.natAdd q u = j) ?_ ?_ j
    · intro a eq
      have lengths := congrArg List.length eq
      have bound := long a
      simp [singletonExtendedRows] at lengths
      omega
    · intro v eq
      have same : u = v := by simpa [singletonExtendedRows] using eq
      exact congrArg (Fin.natAdd q) same

private theorem singletonExtendedRows_bridgeFree {n q k : ℕ} {paths : Fin q → List (Fin n)}
    (free : BridgeFree (Before paths) k) : BridgeFree (Before (singletonExtendedRows paths)) k := by
  intro s size
  refine ⟨fun b => ?_⟩
  have existing {i : Fin (q+n)} {x y : Fin n} (h : Before (singletonExtendedRows paths) i x y) :
      i.val < q := by
    refine Fin.addCases (motive := fun i => Before (singletonExtendedRows paths) i x y → i.val < q)
      (fun j _ => j.isLt) ?_ i h
    intro v step
    have points : x = v ∧ y = v := by
      simpa [singletonExtendedRows] using And.intro step.1 step.2.1
    exact (listBefore_ne step (points.1.trans points.2.symm)).elim
  have project {i : Fin (q+n)} {x y : Fin n}
      (step : Before (singletonExtendedRows paths) i x y) :
      Before paths (⟨i.val,existing step⟩ : Fin q) x y := by
    let previous : Fin q := ⟨i.val,existing step⟩
    have eq : Fin.castAdd n previous = i := Fin.ext rfl
    have row : singletonExtendedRows paths i = paths previous := by
      calc
        _ = singletonExtendedRows paths (Fin.castAdd n previous) := congrArg _ eq.symm
        _ = _ := by simp [singletonExtendedRows]
    unfold SourceAudit.BeforeIn at *
    exact row ▸ step
  apply (free size).false
  refine ⟨b.vertex,(fun i => ⟨(b.arc i).val,existing (b.arcStep i)⟩),
    ⟨b.river.val,existing b.riverStep⟩,b.distinctVertices,?_,?_,project b.riverStep,
    fun i => project (b.arcStep i)⟩
  · intro i j eq
    exact b.distinctArcs (Fin.ext (congrArg (Fin.val : Fin q → ℕ) eq))
  · intro i eq
    exact b.river_ne_arc i (Fin.ext (congrArg (Fin.val : Fin q → ℕ) eq))

private theorem singletonExtendedRows_degree {n q : ℕ} (paths : Fin q → List (Fin n)) (v : Fin n) :
    (occurrences (fun i => (singletonExtendedRows paths i).toFinset) v).card =
      (occurrences (fun i => (paths i).toFinset) v).card + 1 := by
  let original := occurrences (fun i => (paths i).toFinset) v
  let expand : Fin q ↪ Fin (q+n) := ⟨Fin.castAdd n,fun _ _ eq =>
    Fin.ext (congrArg (Fin.val : Fin (q+n) → ℕ) eq)⟩
  let extra := Fin.natAdd q v
  have different : extra ∉ original.map expand := by
    intro member
    obtain ⟨i,_,eq⟩ := mem_map.mp member
    have numeric : i.val = q+v.val := congrArg Fin.val eq
    omega
  have eq : occurrences (fun i => (singletonExtendedRows paths i).toFinset) v =
      insert extra (original.map expand) := by
    ext i
    refine Fin.addCases (motive := fun i => i ∈ occurrences (fun i => (singletonExtendedRows paths i).toFinset) v ↔
        i ∈ insert extra (original.map expand)) ?_ ?_ i
    · intro j
      have notAdded : Fin.castAdd n j ≠ extra := by
        intro same
        have numeric : j.val = q+v.val := congrArg Fin.val same
        omega
      rw [mem_insert,or_iff_right notAdded,mem_map]
      constructor
      · intro member
        refine ⟨j,?_,rfl⟩
        simpa [mem_occurrences,singletonExtendedRows,original] using member
      · rintro ⟨a,member,same⟩
        have eq : a = j := expand.injective same
        simpa [mem_occurrences,singletonExtendedRows,original,eq] using member
    · intro u
      have none : Fin.natAdd q u ∉ original.map expand := by
        intro member
        obtain ⟨j,_,same⟩ := mem_map.mp member
        have numeric : j.val = q+u.val := congrArg Fin.val same
        omega
      rw [mem_insert,or_iff_left none]
      simp [mem_occurrences,singletonExtendedRows,extra,eq_comm]
  rw [eq,card_insert_of_notMem different,card_map]

private theorem singletonExtendedRows_length {n q : ℕ} {paths : Fin q → List (Fin n)}
    (length : ∀ i, (paths i).length = 2) (i : Fin (q+n)) :
    1 ≤ (singletonExtendedRows paths i).length ∧ (singletonExtendedRows paths i).length ≤ 2 := by
  refine Fin.addCases (motive := fun i => 1 ≤ (singletonExtendedRows paths i).length ∧
    (singletonExtendedRows paths i).length ≤ 2) ?_ ?_ i
  · intro j
    simp [singletonExtendedRows,length j]
  · intro v
    simp [singletonExtendedRows]

private theorem frozen_cleaning_distinct_singletons {n p M k : ℕ} (hn : 0 < n) (ordered : n ≤ p)
    (dense : n ≤ M) (long : p ≤ M) (small : M ≤ 4*n) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let clean (i : Fin n) := [i]
  have simple (i : Fin n) : (clean i).Nodup := by simp [clean]
  have injective : Function.Injective clean := by
    intro i j eq
    simpa [clean] using eq
  have free : BridgeFree (Before clean) k := by
    intro s _
    refine ⟨fun b => listBefore_ne b.riverStep ?_⟩
    exact (List.mem_singleton.mp b.riverStep.1).trans (List.mem_singleton.mp b.riverStep.2.1).symm
  have mass : (∑ i, (clean i).length) = n := by simp [clean]
  have degree (v : Fin n) : occurrences (fun i => (clean i).toFinset) v = {v} := by
    ext i
    simp [mem_occurrences,clean,eq_comm]
  have hp : 0 < p := hn.trans_le ordered
  have hnReal : (0:ℝ) < n := by exact_mod_cast hn
  have hpReal : (0:ℝ) < p := by exact_mod_cast hp
  refine ⟨n,le_rfl,n,ordered,clean,injective,by simp [clean],simple,free,?_,?_,?_⟩
  · rw [mass]
    omega
  · rwa [mass]
  · constructor
    · intro v
      rw [degree,card_singleton,Nat.cast_one]
      exact ⟨(div_le_iff₀ (by positivity : 0 < (4:ℝ)*n)).mpr (by
        simpa using (Nat.cast_le.mpr small : (M:ℝ) ≤ (4*n : ℕ))),
        (le_div_iff₀ hnReal).mpr (by
          have d : (n:ℝ) ≤ M := by exact_mod_cast dense
          linarith)⟩
    · intro i
      rw [show (clean i).length = 1 from rfl,Nat.cast_one]
      have lengthLow : (M:ℝ) ≤ 4*(p:ℝ) := by exact_mod_cast small.trans (Nat.mul_le_mul_left 4 ordered)
      have lengthHigh : (p:ℝ) ≤ M := by exact_mod_cast long
      exact ⟨(div_le_iff₀ (by positivity)).mpr (by linarith),
        (le_div_iff₀ hpReal).mpr (by linarith)⟩

private theorem frozen_cleaning_distinct_odd_block {h p M k : ℕ} (hPos : 0 < h)
    (pathRoom : (2*h+1)*h < p) (long : p ≤ M) (massHigh : M ≤ 4*p)
    (degreeLow : M ≤ 4*((2*h+1)*(h+1))) (degreeFits : (2*h+1)*(h+1) ≤ M) :
    ∃ n' ≤ 2*h+1, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps (2*h+1) p M clean := by
  let paths := frozenRectangleRows 1 h
  let clean := singletonExtendedRows paths
  have hp : 0 < p := Nat.zero_lt_of_lt pathRoom
  have rowLength (i : Fin (1*(h*h))) : (paths i).length = 2 := by simp [paths,frozenRectangleRows]
  have lengths (i : Fin (1*(h*h)+1*(2*h))) : 1 ≤ (clean i).length ∧ (clean i).length ≤ 2 :=
    singletonExtendedRows_length rowLength i
  have nonempty (i : Fin (1*(h*h)+1*(2*h))) : clean i ≠ [] := by
    intro eq
    simpa [eq] using (lengths i).1
  have pCap : 1*(h*h)+1*(2*h) ≤ p := by
    have one : h ≤ h*h := by simpa using Nat.mul_le_mul_right h (Nat.succ_le_of_lt hPos)
    calc
      _ ≤ (2*h+1)*h := by simp only [Nat.one_mul]; nlinarith only [one]
      _ ≤ p := pathRoom.le
  have mass : (∑ i, (clean i).length) = (2*h)*(h+1) := by
    rw [Fin.sum_univ_add]
    simp [clean,singletonExtendedRows,rowLength]
    ring
  have degree (v : Fin (1*(2*h))) :
      (occurrences (fun i => (clean i).toFinset) v).card = h+1 := by
    rw [singletonExtendedRows_degree,frozenRectangleRows_degree]
  have free : BridgeFree (Before paths) k := frozenRectangleRows_free 1 h k
  have simple := frozenRectangleRows_simple (r := 1) (w := h)
  have inj : Function.Injective paths := nontrivial_halfFree_paths_injective simple
    (fun i => (rowLength i).symm ▸ le_rfl) (k := 2) le_rfl (frozenRectangleRows_free 1 h 2).halfFree
  refine ⟨1*(2*h),by omega,_,pCap,clean,
    singletonExtendedRows_injective inj (fun i => (rowLength i).symm ▸ le_rfl),nonempty,
    singletonExtendedRows_simple simple,singletonExtendedRows_bridgeFree free,?_,?_,?_⟩
  · rw [mass]
    have size : 2*h+1 ≤ 2*(2*h) := by omega
    calc
      M ≤ 4*((2*h+1)*(h+1)) := degreeLow
      _ ≤ 4*((2*(2*h))*(h+1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ size)
      _ = _ := by ring
  · rw [mass]
    exact (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans degreeFits
  · constructor
    · intro v
      rw [degree]
      have nPos : (0:ℝ) < ((2*h+1 : ℕ):ℝ) := by positivity
      have low : M ≤ (h+1)*(4*(2*h+1)) := degreeLow.trans_eq (by ring)
      have high : (h+1)*(2*h+1) ≤ 4*M := by
        rw [Nat.mul_comm]
        omega
      exact ⟨(div_le_iff₀ (by positivity)).mpr (by exact_mod_cast low),
        (le_div_iff₀ nPos).mpr (by exact_mod_cast high)⟩
    · intro i
      have hpReal : (0:ℝ) < p := by exact_mod_cast hp
      have low : (M:ℝ)/(4*(p:ℝ)) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by
        have cap : (M:ℝ) ≤ 4*(p:ℝ) := by exact_mod_cast massHigh
        linarith)
      have high : (2:ℝ) ≤ 4*(M:ℝ)/(p:ℝ) := (le_div_iff₀ hpReal).mpr (by
        have cap : (p:ℝ) ≤ M := by exact_mod_cast long
        linarith)
      have atMost : ((clean i).length:ℝ) ≤ 2 := by exact_mod_cast (lengths i).2
      exact ⟨low.trans (by exact_mod_cast (lengths i).1),atMost.trans high⟩

/-- At an original mean length of at most four, a literal set of simple
nonempty paths has a distinct witness satisfying all four original caps.
The witness can exclude full bridges through any chosen cutoff. -/
theorem regularization_list_frozen_distinct_of_small_mean {n p k : ℕ} (outputCutoff : ℕ)
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : (∑ i, (paths i).length) ≤ 4*p) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) outputCutoff ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases order : p ≤ n
  · exact full_frozen_cleaning_sparse_disjoint (factor := 4) le_rfl hp order dense
      (small.trans (Nat.mul_le_mul_left _ order))
  have ordered : n ≤ p := le_of_not_ge order
  by_cases sparse : M ≤ 4*n
  · exact frozen_cleaning_distinct_singletons hn ordered dense long sparse
  let w := (M+4*n-1)/(4*n)
  let h := w-1
  obtain ⟨wPos,cover,rounded⟩ := quarterMean_ceiling hn (hn.trans_le dense)
  change 0 < w at wPos
  change M ≤ 4*n*w at cover
  change 4*n*w ≤ M+4*n-1 at rounded
  have widthAtLeastTwo : 2 ≤ w := by
    by_contra smallWidth
    have widthOne : w = 1 := by omega
    rw [widthOne,Nat.mul_one] at cover
    exact sparse cover
  have wEq : w = h+1 := by dsimp [h]; omega
  have hPos : 0 < h := by omega
  have candidate : 4*n*h < M := by
    rw [wEq,Nat.mul_succ] at rounded
    omega
  have charge : n*h < p := by
    rw [Nat.mul_assoc] at candidate
    omega
  have degreeLow : M ≤ 4*(n*w) := by rwa [← Nat.mul_assoc]
  have degreeFits : n*w ≤ M := by
    rw [Nat.mul_assoc] at rounded
    change n ≤ M at dense
    omega
  have rowCount := distinctPathCount_le_square paths distinct nonempty simple two free
  have comparison : M ≤ n*(n-1)+p := listMass_le_ordered_pairs_add_paths paths simple free two
  have massCap : M ≤ 2*(n*n) := by
    have pairs := Nat.mul_le_mul_left n (show n-1 ≤ n by omega)
    rw [pow_two] at rowCount
    omega
  have eitherWidth : 2*w ≤ n+1 := by
    by_contra impossible
    have larger : n ≤ 2*h := by omega
    have multiply := Nat.mul_le_mul_left (2*n) larger
    have impossibleMass : 2*(n*n) ≤ 4*n*h := by
      calc
        _ = (2*n)*n := by ring
        _ ≤ (2*n)*(2*h) := multiply
        _ = _ := by ring
    omega
  by_cases fits : 2*w ≤ n
  · have square : w*w ≤ p := by
      calc
        w*w ≤ w*(2*h) := Nat.mul_le_mul_left _ (by omega)
        _ = (2*w)*h := by ring
        _ ≤ n*h := Nat.mul_le_mul_right _ fits
        _ ≤ p := charge.le
    obtain ⟨v,vCap,q,qCap,clean,cleanSimple,rowLen,cleanFree,mass,upper,caps⟩ :=
      frozen_cleaning_bipartite_rows_length_two wPos hp fits square long
        (show M ≤ 8*p by change M ≤ 4*p at small; omega) degreeLow degreeFits (k := max 2 outputCutoff)
    have cleanDistinct : Function.Injective clean := by
      have twoOrMore (i : Fin q) : 2 ≤ (clean i).length := by rw [rowLen i]
      exact nontrivial_halfFree_paths_injective cleanSimple twoOrMore (le_max_left _ _) cleanFree.halfFree
    exact ⟨v,vCap,q,qCap,clean,cleanDistinct,(fun i empty => by simpa [empty] using rowLen i),
      cleanSimple,(fun _ size => cleanFree (size.trans (le_max_right _ _))),mass,upper,caps⟩
  have odd : n = 2*h+1 := by omega
  have oddCharge : (2*h+1)*h < p := by rwa [← odd]
  have oddLow : M ≤ 4*((2*h+1)*(h+1)) := by simpa only [← odd,← wEq] using degreeLow
  have oddFits : (2*h+1)*(h+1) ≤ M := by simpa only [← odd,← wEq] using degreeFits
  simpa only [← odd] using frozen_cleaning_distinct_odd_block (k := outputCutoff) hPos oddCharge
    long small oddLow oddFits

/-- A frozen witness in the indexed model transfers to the literal simple-path
set model at any cutoff of at least two. -/
theorem regularization_list_frozen_distinct_of_indexed {n p k retention : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (retentionBound : 8 ≤ retention)
    (indexed : let M := ∑ i, (paths i).length; p ≤ M →
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  have long : p ≤ M := by
    calc
      _ = ∑ i : Fin p, (1:ℕ) := by simp
      _ ≤ _ := sum_le_sum fun i _ => List.length_pos_of_ne_nil (nonempty i)
  have halfFromAllowed {v q : ℕ} {family : Fin q → List (Fin v)}
      (legal : localOrderAdmissible half k family) : HalfBridgeFree (Before family) k := by
    cases half
    · exact (show BridgeFree (Before family) k from legal).halfFree
    · exact legal
  by_cases small : M ≤ 4*p
  · obtain ⟨v,vCap,q,qCap,clean,injective,present,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_distinct_of_small_mean k paths distinct nonempty simple
        (halfFromAllowed allowed) two hn hp dense long small
    have cleanAllowed : localOrderAdmissible half k clean := by
      cases half
      · exact cleanFree
      · exact cleanFree.halfFree
    exact ⟨v,vCap,q,qCap,clean,injective,present,cleanSimple,cleanAllowed,
      mass.trans (Nat.mul_le_mul_right _ retentionBound),upper,caps⟩
  obtain ⟨v,vCap,q,qCap,clean,cleanSimple,cleanAllowed,mass,upper,caps⟩ := indexed long
  obtain ⟨injective,present⟩ := frozen_length_distinct_of_large_mean cleanSimple (halfFromAllowed cleanAllowed)
    two hp (lt_of_not_ge small) caps
  exact ⟨v,vCap,q,qCap,clean,injective,present,cleanSimple,cleanAllowed,mass,upper,caps⟩

/-- At half cutoff four, the frozen caps also admit a literal set of
distinct nonempty simple paths whenever the input is such a set. -/
theorem regularization_list_frozen_half_four_distinct {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 4) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := true) paths distinct nonempty simple free (by decide)
    hn hp dense (by decide) (regularization_list_frozen_half_four paths simple free hn hp dense)

/-- The frozen full-bridge cleaning through five also admits a distinct
nonempty witness in the literal path set model. -/
theorem regularization_list_frozen_full_short_distinct {n p k : ℕ} (three : 3 ≤ k) (five : k ≤ 5)
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) paths distinct nonempty simple free (by omega)
    hn hp dense (by decide) (regularization_list_frozen_full_short three five paths simple free hn hp dense)

/-- The all-size full-bridge cleaning also has distinct nonempty output. -/
theorem regularization_list_frozen_full_all_distinct {n p : ℕ} (paths : Fin p → List (Fin n))
    (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ []) (simple : ∀ i, (paths i).Nodup)
    (free : ∀ d, IsEmpty (Bridge (Before paths) d)) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
      (∀ i, (clean i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before clean) d)) ∧
      M ≤ 40*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let k := max 2 (min n p)
  have inputFree : BridgeFree (Before paths) k := fun d _ => free d
  obtain ⟨v,vCap,q,qCap,clean,injective,present,cleanSimple,cleanFree,mass,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (half := false) (retention := 40) paths distinct
      nonempty simple inputFree (le_max_left _ _) hn hp dense (by decide) (fun long => by
        obtain ⟨v,vc,q,qc,clean,nodup,allowed,mass,upper,caps⟩ :=
          regularization_list_frozen_full_all paths simple free hn hp dense long
        exact ⟨v,vc,q,qc,clean,nodup,(fun d _ => allowed d),mass,upper,caps⟩)
  exact ⟨v,vCap,q,qCap,clean,injective,present,cleanSimple,
    bridgeFree_all_of_cutoff_ge_min cleanFree ((min_le_min vCap qCap).trans (le_max_right _ _)),mass,upper,caps⟩

/-- The half-four cleaning bound relative to the literal exact-count
maximum, whenever the original budgets admit an eligible family. -/
theorem localOrderDistinctExtremal_frozen_half_four {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 4) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 4 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 4 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
        (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 4 ∧
        M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,distinct,rows,free,maximal,dense,_⟩ :=
    localOrderDistinctExtremal_isDense (k := 4) true hp feasible
  exact ⟨paths,distinct,rows,free,maximal,regularization_list_frozen_half_four_distinct paths distinct
    (fun i => (rows i).1) (fun i => (rows i).2) free hn hp dense⟩

/-- The full cleaning bound through cutoff five relative to the literal
exact-count maximum, for feasible original budgets. -/
theorem localOrderDistinctExtremal_frozen_full_short {n p k : ℕ} (three : 3 ≤ k) (five : k ≤ 5)
    (hn : 0 < n) (hp : 0 < p)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) k) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) k ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) k →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧
        (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
        M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,distinct,rows,free,maximal,dense,_⟩ :=
    localOrderDistinctExtremal_isDense (k := k) false hp feasible
  exact ⟨paths,distinct,rows,free,maximal,regularization_list_frozen_full_short_distinct three five paths distinct
    (fun i => (rows i).1) (fun i => (rows i).2) free hn hp dense⟩

end OnlineReachabilityPreservers
