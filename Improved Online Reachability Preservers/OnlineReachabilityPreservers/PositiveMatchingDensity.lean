import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import OnlineReachabilityPreservers.HalfThreeUpstreamMass
import OnlineReachabilityPreservers.ThreeBlockMatchingReduction

/-! Positive matching color classes have subquadratic total size with a linear palette. -/

namespace OnlineReachabilityPreservers

open Finset SimpleGraph SimpleGraph.TripartiteFromTriangles
open scoped Prod.Lex

private theorem card_few_predecessors_le {E : Type*} [LinearOrder E] (s : Finset E) (m : ℕ) :
    (s.filter fun x => (s.filter fun y => y < x).card < m).card ≤ m := by
  calc
    _ ≤ (range m).card := by
      apply card_le_card_of_injOn (fun x => (s.filter fun y => y < x).card)
      · intro x on
        exact mem_range.mpr (mem_filter.mp on).2
      · intro x hx y hy equal
        have increasing {a b : E} (ha : a ∈ s) (lt : a < b) :
            (s.filter fun z => z < a).card < (s.filter fun z => z < b).card := by
          apply card_lt_card
          refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨a, mem_filter.mpr ⟨ha,lt⟩, by simp⟩
          intro z on
          have h := mem_filter.mp on
          exact mem_filter.mpr ⟨h.1,h.2.trans lt⟩
        rcases lt_trichotomy x y with lt | eq | gt
        · exact ((increasing (mem_filter.mp hx).1 lt).ne equal).elim
        · exact eq
        · exact ((increasing (mem_filter.mp hy).1 gt).ne equal.symm).elim
    _ = m := card_range m

private theorem no_edges_large_subsets {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ} {U V' X Y : Finset V}
    (uniform : G.IsUniform ε U V') (dense : 2*ε ≤ (G.edgeDensity U V' : ℝ))
    (positive : 0 < ε) (xU : X ⊆ U) (yV : Y ⊆ V')
    (largeX : (U.card:ℝ)*ε ≤ X.card) (largeY : (V'.card:ℝ)*ε ≤ Y.card)
    (noEdges : ∀ ⦃x y⦄, x ∈ X → y ∈ Y → ¬ G.Adj x y) : False := by
  have empty : G.interedges X Y = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro ⟨x,y⟩ on
    obtain ⟨hx,hy,edge⟩ := (G.mem_interedges_iff.mp on)
    exact noEdges hx hy edge
  have zero : G.edgeDensity X Y = 0 := by rw [edgeDensity_def, empty]; simp
  have close := uniform xU yV largeX largeY
  have nonnegative : (0:ℝ) ≤ G.edgeDensity U V' := by linarith only [dense,positive]
  rw [zero,Rat.cast_zero,zero_sub,abs_neg,abs_of_nonneg nonnegative] at close
  linarith only [close,dense,positive]

/-- If crossing an ordered matching backwards is impossible in the original graph,
its edges in the regularity reduction must sit at an end of the matching within
one of their two parts. The two end sets are charged once per part. -/
private theorem ordered_matching_reduced_card_le {V E : Type*} [DecidableEq V] [Fintype V]
    [LinearOrder E] (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    (ε : ℝ) (positive : 0 < ε) (s : Finset E) (left right : E → V)
    (injectLeft : Set.InjOn left s) (injectRight : Set.InjOn right s)
    (noBackward : ∀ ⦃a b⦄, a ∈ s → b ∈ s → b < a → ¬ G.Adj (left a) (right b)) :
    (((s.filter fun e => (G.regularityReduced P ε (2*ε)).Adj (left e) (right e)).card):ℝ) ≤
      2*(ε*(Fintype.card V:ℝ)+(P.parts.card:ℝ)) := by
  classical
  let kept := s.filter fun e => (G.regularityReduced P ε (2*ε)).Adj (left e) (right e)
  let leftIn (U : Finset V) := s.filter fun e => left e ∈ U
  let rightIn (U : Finset V) := s.filter fun e => right e ∈ U
  let quota (U : Finset V) := ⌈(U.card:ℝ)*ε⌉₊
  let leftEnd (U : Finset V) := (leftIn U).filter fun e => ((leftIn U).filter fun f => e < f).card < quota U
  let rightEnd (U : Finset V) := (rightIn U).filter fun e => ((rightIn U).filter fun f => f < e).card < quota U
  have cover : kept ⊆ (P.parts.biUnion leftEnd) ∪ P.parts.biUnion rightEnd := by
    intro e he
    obtain ⟨_,U,hU,W,hW,lU,rW,_,uniform,dense⟩ := (mem_filter.mp he).2
    by_cases smallL : ((leftIn U).filter fun f => e < f).card < quota U
    · exact mem_union.mpr (Or.inl (mem_biUnion.mpr ⟨U,hU,mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp he).1,lU⟩,smallL⟩⟩))
    by_cases smallR : ((rightIn W).filter fun f => f < e).card < quota W
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨W,hW,mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp he).1,rW⟩,smallR⟩⟩))
    exfalso
    let later := (leftIn U).filter fun f => e < f
    let earlier := (rightIn W).filter fun f => f < e
    let X := later.image left
    let Y := earlier.image right
    have lMem {f} (on : f ∈ later) := mem_filter.mp (mem_filter.mp on).1
    have rMem {f} (on : f ∈ earlier) := mem_filter.mp (mem_filter.mp on).1
    have lx : X ⊆ U := by
      intro x on
      obtain ⟨f,hf,rfl⟩ := mem_image.mp on
      exact (lMem hf).2
    have ry : Y ⊆ W := by
      intro y on
      obtain ⟨f,hf,rfl⟩ := mem_image.mp on
      exact (rMem hf).2
    have xSize : X.card = later.card := card_image_of_injOn fun _ a _ b => injectLeft (lMem a).1 (lMem b).1
    have ySize : Y.card = earlier.card := card_image_of_injOn fun _ a _ b => injectRight (rMem a).1 (rMem b).1
    refine no_edges_large_subsets uniform dense positive lx ry ?_ ?_ ?_
    · rw [xSize]
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_of_not_gt smallL))
    · rw [ySize]
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_of_not_gt smallR))
    · intro x y hx hy
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      exact noBackward (lMem ha).1 (rMem hb).1 ((mem_filter.mp hb).2.trans (mem_filter.mp ha).2)
  have ends (U : Finset V) : (leftEnd U).card ≤ quota U ∧ (rightEnd U).card ≤ quota U :=
    ⟨card_few_predecessors_le (E := Eᵒᵈ) (leftIn U) (quota U), card_few_predecessors_le (rightIn U) (quota U)⟩
  have unionBound (which : Finset V → Finset E) (each : ∀ U, (which U).card ≤ quota U) :
      ((P.parts.biUnion which).card:ℝ) ≤ ε*(Fintype.card V:ℝ)+(P.parts.card:ℝ) := calc
    _ ≤ ∑ U ∈ P.parts, ((which U).card:ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ U ∈ P.parts, ((U.card:ℝ)*ε+1) := sum_le_sum fun U _ =>
      (Nat.cast_le.mpr (each U)).trans ((Nat.ceil_lt_add_one (by positivity)).le)
    _ = _ := by
      have total : (∑ U ∈ P.parts, (U.card:ℝ)) = Fintype.card V := by
        exact_mod_cast (P.sum_card_parts.trans card_univ)
      rw [sum_add_distrib,← sum_mul,total]
      simp [mul_comm]
  calc
    (kept.card:ℝ) ≤ ((P.parts.biUnion leftEnd ∪ P.parts.biUnion rightEnd).card:ℝ) := Nat.cast_le.mpr (card_le_card cover)
    _ ≤ ((P.parts.biUnion leftEnd).card:ℝ) + ((P.parts.biUnion rightEnd).card:ℝ) := by exact_mod_cast card_union_le _ _
    _ ≤ _ := by linarith only [unionBound leftEnd (fun U => (ends U).1), unionBound rightEnd (fun U => (ends U).2)]

private def positiveBipartiteGraph {n : ℕ} (t : Finset (Fin n × Fin n × Fin n)) : SimpleGraph (Fin n ⊕ Fin n) :=
  SimpleGraph.fromRel fun a b => match a, b with
    | .inl a, .inr b => ∃ c, (a,b,c) ∈ t
    | _, _ => False

private theorem positiveBipartiteGraph_adj {n : ℕ} (t : Finset (Fin n × Fin n × Fin n)) (a b : Fin n) :
    (positiveBipartiteGraph t).Adj (.inl a) (.inr b) ↔ ∃ c, (a,b,c) ∈ t := by
  simp [positiveBipartiteGraph]

private theorem positive_fiber_reduced_card_le {n : ℕ} (t : Finset (Fin n × Fin n × Fin n))
    [ExplicitDisjoint t] [DecidableRel (positiveBipartiteGraph t).Adj]
    (left right : Fin n → Fin n → ℝ)
    (positive : ∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t))
    (P : Finpartition (univ : Finset (Fin n ⊕ Fin n))) (ε : ℝ) (εPos : 0 < ε) (c : Fin n) :
    (((t.filter (fun x => (positiveBipartiteGraph t).regularityReduced P ε (2*ε) |>.Adj
        (.inl x.1) (.inr x.2.1))).filter fun x => x.2.2 = c).card:ℝ) ≤
      2*(ε*(2*(n:ℝ))+(P.parts.card:ℝ)) := by
  classical
  let key (x : Fin n × Fin n × Fin n) := toLex (left c x.1,Fintype.equivFin _ x)
  let order : LinearOrder (Fin n × Fin n × Fin n) := LinearOrder.lift' key fun x y same =>
    (Fintype.equivFin _).injective (congrArg (fun q => (ofLex q).2) same)
  let fiber := t.filter (fun x => x.2.2 = c)
  have on {x} (hx : x ∈ fiber) : (x.1,x.2.1,c) ∈ t := by
    rcases x with ⟨a,b,d⟩
    obtain ⟨member,hd⟩ := mem_filter.mp hx
    change d = c at hd
    subst d
    exact member
  have inLeft : Set.InjOn (fun x : Fin n × Fin n × Fin n => Sum.inl x.1 : _ → Fin n ⊕ Fin n) fiber := by
    intro x hx y hy same
    have a := Sum.inl.inj same
    have b : x.2.1 = y.2.1 := ExplicitDisjoint.inj₁ (a ▸ on hx) (on hy)
    exact Prod.ext a (Prod.ext b ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm))
  have inRight : Set.InjOn (fun x : Fin n × Fin n × Fin n => Sum.inr x.2.1 : _ → Fin n ⊕ Fin n) fiber := by
    intro x hx y hy same
    have b := Sum.inr.inj same
    have a : x.1 = y.1 := ExplicitDisjoint.inj₀ (b ▸ on hx) (on hy)
    exact Prod.ext a (Prod.ext b ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm))
  have noBackward ⦃a b⦄ (ha : a ∈ fiber) (hb : b ∈ fiber) (earlier : @LT.lt _ order.toLT b a) :
      ¬ (positiveBipartiteGraph t).Adj (.inl a.1) (.inr b.2.1) := by
    intro crossed
    have weightOrder : left c b.1 ≤ left c a.1 := by
      rcases Prod.Lex.toLex_lt_toLex.mp (show key b < key a from earlier) with lt | ⟨eq,_⟩
      · exact lt.le
      · exact eq.le
    have hbPos := (positive b.1 b.2.1 c ⟨c,on hb⟩).mpr (on hb)
    have crossPos : 0 < left c a.1 + right c b.2.1 := by linarith only [hbPos,weightOrder]
    have crossOn := (positive a.1 b.2.1 c ((positiveBipartiteGraph_adj t _ _).mp crossed)).mp crossPos
    have same : a.1 = b.1 := ExplicitDisjoint.inj₀ crossOn (on hb)
    exact (show key b < key a from earlier).ne (congrArg key (inLeft hb ha (congrArg Sum.inl same.symm)))
  have bound := @ordered_matching_reduced_card_le _ _ _ _ order (positiveBipartiteGraph t) _ P ε εPos
    fiber _ _ inLeft inRight noBackward
  simpa only [fiber,filter_filter,and_comm,Fintype.card_sum,Fintype.card_fin,Nat.cast_add,two_mul] using bound

/-- Positive matching fibers on two `n`-vertex sides with `n` colors
have subquadratic total size. A regularity reduction discards few edges,
and each remaining fiber fits in its partwise first and last sets. -/
theorem positive_matchings_subquadratic (ε : ℝ) (εPos : 0 < ε) :
    ∃ N : ℕ, ∀ {n : ℕ}, N ≤ n → ∀ (t : Finset (Fin n × Fin n × Fin n)) [ExplicitDisjoint t]
      (left right : Fin n → Fin n → ℝ),
      (∀ a b c, (∃ c', (a,b,c') ∈ t) → (0 < left c a+right c b ↔ (a,b,c) ∈ t)) →
      (t.card:ℝ) ≤ ε*(n:ℝ)^2 := by
  classical
  let error := ε/8
  let regularity := error/8
  let lower := ⌈4 / error⌉₊
  let upper := SzemerediRegularity.bound regularity lower
  have errorPos : 0 < error := by dsimp [error]; positivity
  have regPos : 0 < regularity := by dsimp [regularity]; positivity
  refine ⟨lower+⌈(upper:ℝ)/error⌉₊+1,?_⟩
  intro n large t disjoint left right positive
  let V := Fin n ⊕ Fin n
  let G := positiveBipartiteGraph t
  let _ : DecidableRel G.Adj := Classical.decRel _
  have nPos : 0 < n := by omega
  let _ : Nonempty V := ⟨.inl ⟨0,nPos⟩⟩
  have vertexCount : Fintype.card V = 2*n := by simp [V,two_mul]
  obtain ⟨P,equipart,atLeast,atMost,uniform⟩ := szemeredi_regularity G regPos
    (show lower ≤ Fintype.card V by rw [vertexCount]; omega)
  let reduced := G.regularityReduced P regularity (2*regularity)
  have density : 2*regularity = error/4 := by dsimp [regularity]; ring
  have enoughParts : 4 / error ≤ (P.parts.card:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr atLeast)
  have reducedLe : reduced ≤ G := regularityReduced_le
  have losses : (G.edgeFinset.card:ℝ)-(reduced.edgeFinset.card:ℝ) < error*((2*(n:ℝ))^2) := by
    have loss := regularityReduced_edges_card_aux errorPos equipart uniform enoughParts
    rw [← density,vertexCount,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] at loss
    exact lt_of_mul_lt_mul_left (by simpa only [mul_assoc] using loss) zero_le_two
  let kept := t.filter fun x => reduced.Adj (.inl x.1) (.inr x.2.1)
  have keptSub : kept ⊆ t := filter_subset _ _
  let edge (x : Fin n × Fin n × Fin n) : Sym2 V := s(Sum.inl x.1, Sum.inr x.2.1)
  have lossCount : (t \ kept).card ≤ (G.edgeFinset \ reduced.edgeFinset).card := by
    apply card_le_card_of_injOn edge
    · intro x hx
      have h := mem_sdiff.mp hx
      apply mem_sdiff.mpr
      simp only [edge,mem_edgeFinset,mem_edgeSet]
      refine ⟨(positiveBipartiteGraph_adj t _ _).mpr ⟨x.2.2,by simpa only [Prod.eta] using h.1⟩,?_⟩
      exact fun adj => h.2 (mem_filter.mpr ⟨h.1,adj⟩)
    · rintro ⟨a,b,c⟩ hx ⟨a',b',c'⟩ hy he
      have hp := Sym2.eq_iff.mp he
      rcases hp with ⟨l,r⟩ | ⟨l,_⟩
      · cases Sum.inl.inj l
        cases Sum.inr.inj r
        exact congrArg (fun d => (a,b,d)) (ExplicitDisjoint.inj₂ (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1)
      · cases l
  rw [card_sdiff_of_subset keptSub,card_sdiff_of_subset (edgeFinset_mono reducedLe)] at lossCount
  have removed : (t.card:ℝ)-(kept.card:ℝ) < error*((2*(n:ℝ))^2) := by
    have bound : ((t.card-kept.card:ℕ):ℝ) ≤ ((G.edgeFinset.card-reduced.edgeFinset.card:ℕ):ℝ) :=
      Nat.cast_le.mpr lossCount
    rw [Nat.cast_sub (card_le_card keptSub),Nat.cast_sub (card_le_card (edgeFinset_mono reducedLe))] at bound
    exact bound.trans_lt losses
  have sum : (kept.card:ℝ) = ∑ c : Fin n, ((kept.filter (fun x => x.2.2 = c)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_fiberwise (s := kept) (t := (univ : Finset (Fin n)))
      (f := fun x => x.2.2) (fun x _ => mem_univ x.2.2)
  have partCount : (P.parts.card:ℝ) ≤ error*(n:ℝ) := calc
    _ ≤ (upper:ℝ) := Nat.cast_le.mpr atMost
    _ ≤ error*(n:ℝ) := by
      have enough : (upper:ℝ)/error ≤ (n:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by omega))
      simpa only [mul_comm] using (div_le_iff₀ errorPos).mp enough
  have retained : (kept.card:ℝ) ≤ (n:ℝ)*2*(regularity*(2*(n:ℝ))+error*(n:ℝ)) := calc
    _ ≤ ∑ _c : Fin n, 2*(regularity*(2*(n:ℝ))+error*(n:ℝ)) := by
      rw [sum]
      apply sum_le_sum
      intro c _
      exact (positive_fiber_reduced_card_le t left right positive P regularity regPos c).trans (by gcongr)
    _ = _ := by simp [nsmul_eq_mul]; ring
  dsimp [error,regularity] at removed retained
  nlinarith only [removed,retained,mul_nonneg εPos.le (sq_nonneg (n:ℝ))]

/-- The total length of rows of length at least three in a half-three-free
family is subquadratic in the number of vertices, uniformly in the number
of rows and all cutoffs at least three. -/
theorem half_three_long_mass_subquadratic (ε : ℝ) (εPos : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (SourceAudit.BeforeIn paths) k →
      (listMassAboveWidth paths 2:ℝ) ≤ ε*(n:ℝ)^2 := by
  obtain ⟨N,small⟩ := positive_matchings_subquadratic (ε/5) (by positivity)
  refine ⟨N,?_⟩
  intro n p k large three paths simple free
  obtain ⟨t,_,mass,disjoint,left,right,positive⟩ := half_three_long_mass_positive_matchings paths simple free three
  let _ : ExplicitDisjoint t := disjoint
  calc
    _ ≤ 5*(t.card:ℝ) := by exact_mod_cast mass
    _ ≤ 5*((ε/5)*(n:ℝ)^2) := by gcongr; exact small large t left right positive
    _ = _ := by ring

private theorem mass_le_twice_paths_add_long_mass {V : Type*} {p : ℕ} (paths : Fin p → List V) :
    (∑ i, (paths i).length) ≤ 2*p+listMassAboveWidth paths 2 := calc
  _ ≤ ∑ i, (2+(if 2 < (paths i).length then (paths i).length else 0)) := by
    apply sum_le_sum
    intro i _
    by_cases long : 2 < (paths i).length
    · simp [long]
    · simpa [long] using (le_of_not_gt long)
  _ = _ := by rw [sum_add_distrib]; simp [listMassAboveWidth,sum_filter,Nat.mul_comm]

/-- The total half-three mass is at most `2p + o(n²)`, uniformly in the
row budget. -/
theorem half_three_mass_le_twice_paths_add_subquadratic (ε : ℝ) (εPos : 0 < ε) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (SourceAudit.BeforeIn paths) k →
      ((∑ i, (paths i).length : ℕ):ℝ) ≤ 2*(p:ℝ)+ε*(n:ℝ)^2 := by
  obtain ⟨N,small⟩ := half_three_long_mass_subquadratic ε εPos
  refine ⟨N,?_⟩
  intro n p k large three paths simple free
  have split : ((∑ i, (paths i).length : ℕ):ℝ) ≤ 2*(p:ℝ)+(listMassAboveWidth paths 2:ℝ) := by
    exact_mod_cast mass_le_twice_paths_add_long_mass paths
  exact split.trans (by gcongr; exact small large three paths simple free)

/-- If the starting mean length exceeds eight, half-three-free families
cannot have a fixed positive quadratic mass at unbounded vertex budgets. -/
theorem half_three_high_mean_mass_subquadratic (η : ℝ) (ηPos : 0 < η) :
    ∃ N : ℕ, ∀ {n p k : ℕ}, N ≤ n → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (SourceAudit.BeforeIn paths) k →
      8*p < ∑ i, (paths i).length → ((∑ i, (paths i).length : ℕ):ℝ) < η*(n:ℝ)^2 := by
  obtain ⟨N,small⟩ := half_three_mass_le_twice_paths_add_subquadratic (η/2) (by positivity)
  refine ⟨N,?_⟩
  intro n p k large three paths simple free high
  have bound := small large three paths simple free
  have h : 8*(p:ℝ) < ((∑ i, (paths i).length : ℕ):ℝ) := by exact_mod_cast high
  nlinarith only [bound,h,mul_nonneg ηPos.le (sq_nonneg (n:ℝ))]

/-- For a starting mean length above eight, half-three-free systems have
mass `o(n √p)` as the row budget grows, uniformly in the vertex budget. -/
theorem half_three_high_mean_mass_small_at_large_path_budget (η : ℝ) (ηPos : 0 < η) :
    ∃ P : ℕ, ∀ {n p k : ℕ}, P ≤ p → 3 ≤ k → ∀ paths : Fin p → List (Fin n),
      (∀ i, (paths i).Nodup) → HalfBridgeFree (SourceAudit.BeforeIn paths) k →
      8*p < ∑ i, (paths i).length → ((∑ i, (paths i).length : ℕ):ℝ) < η*(n:ℝ)*Real.sqrt p := by
  obtain ⟨δ,δPos,P,pPos,density⟩ := half_three_n_sqrt_p_mass_requires_quadratic_path_density η ηPos
  obtain ⟨N,small⟩ := half_three_high_mean_mass_subquadratic (8*δ) (by positivity)
  refine ⟨max P (N^2),?_⟩
  intro n p k large three paths simple free high
  have h : 8*(p:ℝ) < ((∑ i, (paths i).length : ℕ):ℝ) := by exact_mod_cast high
  have enough : p ≤ n^2 := by
    have pairs := listMass_le_ordered_pairs_add_paths paths simple free (by omega)
    have cap := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    rw [pow_two]
    omega
  have largeN : N ≤ n := by
    by_contra! smaller
    have fewer : n^2 < N^2 := Nat.pow_lt_pow_left smaller (by decide)
    exact fewer.not_ge ((le_max_right P _).trans large |>.trans enough)
  have nPos : 0 < n := by
    by_contra! zero
    have nZero : n = 0 := by omega
    rw [nZero] at enough
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),Nat.le_zero] at enough
    have := (le_max_left P (N^2)).trans large
    omega
  by_contra! dense
  have required := density nPos ((le_max_left P _).trans large) three paths simple free dense
  have limit := small largeN three paths simple free high
  nlinarith only [required,limit,h]

end OnlineReachabilityPreservers
