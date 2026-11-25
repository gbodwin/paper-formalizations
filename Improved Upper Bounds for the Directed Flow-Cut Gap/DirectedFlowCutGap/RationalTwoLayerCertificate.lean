import DirectedFlowCutGap.RationalEdgeThresholds

/-! Find a rank in `{0,1,2}` at each vertex and check it on every actual arc.
Positive nonloop arcs must strictly increase the rank. All other arcs
must preserve its order, including on graphs with zero-weight cycles. -/
namespace DirectedFlowCutGap.RationalTwoLayerCertificate

open scoped NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)

abbrev Ranks (n : ℕ) := Vector ℕ n

def rise {n : ℕ} (w : Weights n) (u v : Fin n) : ℕ :=
  if u = v then 0 else if (BinaryRational.isZero w[u.val][v.val]).1 then 0 else 1

private theorem rise_of_positive {n : ℕ} (w : Weights n) {u v : Fin n}
    (distinct : u ≠ v) (positive : 0 < weights w (u,v)) : rise w u v = 1 := by
  have nonzero : (BinaryRational.isZero w[u.val][v.val]).1 ≠ true := by
    intro zero
    have numerator := (BinaryRational.isZero_decode _).mp zero
    have eq := (RawNonnegativeRational.Code.value_eq_zero _).mpr numerator
    change 0 < ((BinaryRational.decode w[u.val][v.val]).value : ℝ≥0) at positive
    simp [eq] at positive
  simp [rise,distinct,nonzero]

private def pass {n : ℕ} (A : Adjacency n) (w : Weights n) (previous : Ranks n) : Ranks n :=
  Vector.ofFn fun v =>
    max previous[v.val] (min 3 (Finset.univ.sup fun u : Fin n =>
      if A[u.val][v.val] then previous[u.val] + rise w u v else 0))

private def relax {n : ℕ} (A : Adjacency n) (w : Weights n) : ℕ → Ranks n
  | 0 => Vector.replicate n 0
  | k+1 => pass A w (relax A w k)

def assign {n : ℕ} (A : Adjacency n) (w : Weights n) : Ranks n :=
  relax A w (2*n)

def accepts {n : ℕ} (A : Adjacency n) (w : Weights n) (rank : Ranks n) : Bool :=
  decide ((∀ v : Fin n, rank[v.val] ≤ 2) ∧
    ∀ u v : Fin n, A[u.val][v.val] = true → rank[u.val] + rise w u v ≤ rank[v.val])

theorem accepts_spec {n : ℕ} (A : Adjacency n) (w : Weights n) (rank : Ranks n)
    (ok : accepts A w rank = true) :
    (∀ v : Fin n, rank[v.val] ≤ 2) ∧
    ∀ u v : Fin n, (graph A).Adj u v → rank[u.val] + rise w u v ≤ rank[v.val] :=
  of_decide_eq_true ok

private theorem relax_le {n : ℕ} (A : Adjacency n) (w : Weights n) {rank : Ranks n}
    (ok : accepts A w rank = true) (k : ℕ) (v : Fin n) : (relax A w k)[v.val] ≤ rank[v.val] := by
  obtain ⟨_,edge⟩ := accepts_spec A w rank ok
  induction k generalizing v with
  | zero => simp [relax]
  | succ k ih =>
    simp only [relax,pass,Vector.getElem_ofFn,Fin.eta]
    refine max_le (ih v) (min_le_of_right_le (Finset.sup_le ?_))
    intro u _
    split
    · rename_i connected
      exact (Nat.add_le_add_right (ih u) _).trans (edge u v connected)
    · exact Nat.zero_le _

private theorem relax_mono_step {n : ℕ} (A : Adjacency n) (w : Weights n) (k : ℕ)
    (v : Fin n) : (relax A w k)[v.val] ≤ (relax A w (k+1))[v.val] := by
  simp only [relax,pass,Vector.getElem_ofFn,Fin.eta,le_max_left]

private theorem relax_fixed_of_exists {n : ℕ} (A : Adjacency n) (w : Weights n)
    {rank : Ranks n} (ok : accepts A w rank = true) :
    relax A w (2*n) = relax A w (2*n+1) := by
  let mass (k : ℕ) := ∑ v : Fin n, (relax A w k)[v.val]
  have mass_bound (k : ℕ) : mass k ≤ 2*n := by
    calc
      mass k ≤ ∑ _ : Fin n, 2 := Finset.sum_le_sum fun v _ =>
        (relax_le A w ok k v).trans ((accepts_spec A w rank ok).1 v)
      _ = 2*n := by simp [Nat.mul_comm]
  have stable (k d : ℕ) (fixed : relax A w k = relax A w (k+1)) :
      relax A w (k+d) = relax A w (k+d+1) := by
    induction d with
    | zero => exact fixed
    | succ d ih => exact congrArg (pass A w) ih
  by_contra final
  have advance (k : ℕ) (within : k ≤ 2*n) : mass k < mass (k+1) := by
    refine Finset.sum_lt_sum (fun v _ => relax_mono_step A w k v) ?_
    have changed : ∃ v : Fin n, (relax A w k)[v.val] ≠ (relax A w (k+1))[v.val] := by
      by_contra! same
      have fixed : relax A w k = relax A w (k+1) := by
        ext v hv
        exact same ⟨v,hv⟩
      have last := stable k (2*n-k) fixed
      rw [Nat.add_sub_of_le within] at last
      exact final last
    obtain ⟨v,strict⟩ := changed
    exact ⟨v,Finset.mem_univ _,lt_of_le_of_ne (relax_mono_step A w k v) strict⟩
  have many (k : ℕ) (within : k ≤ 2*n+1) : k ≤ mass k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have prev := ih (by omega)
      have next := advance k (by omega)
      omega
  have impossible := many (2*n+1) le_rfl
  have upper := mass_bound (2*n+1)
  omega

theorem assign_accepts_iff {n : ℕ} (A : Adjacency n) (w : Weights n) :
    accepts A w (assign A w) = true ↔ ∃ rank, accepts A w rank = true := by
  refine ⟨fun ok => ⟨_,ok⟩,?_⟩
  rintro ⟨rank,ok⟩
  have top (v : Fin n) : (assign A w)[v.val] ≤ 2 :=
    (relax_le A w ok _ v).trans ((accepts_spec A w rank ok).1 v)
  refine decide_eq_true ⟨top,?_⟩
  intro u v connected
  have rise_bound : rise w u v ≤ 1 := by
    unfold rise
    split
    · decide
    · split <;> decide
  let incoming (s : Fin n) :=
    if A[s.val][v.val] then (assign A w)[s.val] + rise w s v else 0
  have entry : (assign A w)[u.val] + rise w u v ≤ Finset.univ.sup incoming := by
    have h := Finset.le_sup (f := incoming) (Finset.mem_univ u)
    simpa [incoming,connected] using h
  have arcBound : (assign A w)[u.val] + rise w u v ≤ 3 := by
    have bound := top u
    omega
  have fixed : assign A w = pass A w (assign A w) := relax_fixed_of_exists A w ok
  conv_rhs => rw [fixed]
  simp only [pass,Vector.getElem_ofFn,Fin.eta]
  exact (le_min arcBound entry).trans (le_max_right ..)

def side {n : ℕ} (rank : Ranks n) (e : Fin n × Fin n) : Bool :=
  decide (0 < rank[e.1.val])

/-- Positive arcs on a simple path have distinct colors under any
accepted rank assignment, whether computed here or supplied by a caller. -/
theorem separates {n : ℕ} (A : Adjacency n) (w : Weights n) (rank : Ranks n)
    (ok : accepts A w rank = true) {s t : Fin n} (p : SimplePath (graph A) s t) :
    Set.InjOn (side rank) (↑(p.edges.filter fun e => 0 < weights w e) : Set (Fin n × Fin n)) := by
  obtain ⟨top,arc⟩ := accepts_spec A w rank ok
  let positionRank (i : Fin (p.edgeLength+1)) : ℕ := rank[(p.vertex i).val]
  have bound (i : Fin (p.edgeLength+1)) : positionRank i ≤ 2 := top (p.vertex i)
  have ordered : Monotone positionRank := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact (Nat.le_add_right _ _).trans (arc _ _ (p.adjacent i))
  have strict (i : Fin p.edgeLength) (h : 0 < weights w (p.edgeAt i)) :
      positionRank i.castSucc < positionRank i.succ := by
    have adj := arc _ _ (p.adjacent i)
    have diff := p.edge_ne (p.edgeAt_mem_edges i)
    change rank[(p.vertex i.castSucc).val] + rise w (p.vertex i.castSucc) (p.vertex i.succ) ≤
      rank[(p.vertex i.succ).val] at adj
    have increase : rise w (p.vertex i.castSucc) (p.vertex i.succ) = 1 :=
      rise_of_positive w diff h
    rw [increase] at adj
    exact adj
  have apart {i j : Fin p.edgeLength} (order : i < j)
      (hi : 0 < weights w (p.edgeAt i)) (hj : 0 < weights w (p.edgeAt j)) :
      side rank (p.edgeAt i) ≠ side rank (p.edgeAt j) := by
    have between : i.succ ≤ j.castSucc := by
      change i.val+1 ≤ j.val
      exact Nat.succ_le_of_lt order
    have lower := (strict i hi).trans_le (ordered between)
    have upper := (strict j hj).trans_le (bound j.succ)
    have before : positionRank i.castSucc = 0 := by omega
    have after : positionRank j.castSucc = 1 := by omega
    change decide (0 < positionRank i.castSucc) ≠ decide (0 < positionRank j.castSucc)
    simp [before,after]
  intro e he f hf equal
  obtain ⟨ePath,ePos⟩ := Finset.mem_filter.mp he
  obtain ⟨fPath,fPos⟩ := Finset.mem_filter.mp hf
  obtain ⟨i,rfl⟩ := (p.mem_edges e).mp ePath
  obtain ⟨j,rfl⟩ := (p.mem_edges f).mp fPath
  rcases lt_trichotomy i j with before | same | after
  · exact (apart before ePos fPos equal).elim
  · exact congrArg p.edgeAt same
  · exact (apart after fPos ePos equal.symm).elim

end DirectedFlowCutGap.RationalTwoLayerCertificate
