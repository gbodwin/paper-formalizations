import OnlineReachabilityPreservers.PathAssignments

/-! Cardinality comparison for the rooted pieces used by the early-demand reduction. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]


/-- An inward arborescence, allowing unused ambient vertices. -/
structure InArborescence (T : Arcs V) (root : V) : Prop where
  dag : IsDAG T
  unique_next : ∀ {u v w}, Edge T u v → Edge T u w → v=w
  at_root : ∀ e ∈ T, Reach T e.1 root ∧ Reach T e.2 root

private def towardChoices (G : Arcs V) (root u : V) : Finset V :=
  (reaches G root).filter fun v => Edge G u v ∧ hops G v root < hops G u root

/-- One edge toward the root for each vertex admitting a decreasing route. -/
def targetTree (G : Arcs V) (root : V) : Arcs V :=
  G.filter fun e => least? (towardChoices G root e.1) = some e.2

theorem targetTree_subset (G : Arcs V) (root : V) : targetTree G root ⊆ G := filter_subset _ _

private theorem targetTree_edge {G : Arcs V} {root u v : V} (he : Edge (targetTree G root) u v) :
    Reach G v root ∧ hops G v root < hops G u root := by
  obtain ⟨reach,_,dist⟩ := mem_filter.mp (least?_mem (mem_filter.mp he).2)
  exact ⟨mem_reaches.mp reach,dist⟩

theorem targetTree_reach {G : Arcs V} {root u : V} (reachable : Reach G u root) :
    Reach (targetTree G root) u root := by
  have aux (k : ℕ) (v : V) (eq : hops G v root = k) (reach : Reach G v root) :
      Reach (targetTree G root) v root := by
    induction k using Nat.strong_induction_on generalizing v with
    | _ k ih =>
      by_cases self : v=root
      · rw [self]
      · obtain ⟨w,edge,hw,dist⟩ := exists_decreasing_hop reach self
        have h : (towardChoices G root v).Nonempty :=
          ⟨w,mem_filter.mpr ⟨mem_reaches.mpr hw,edge,dist⟩⟩
        obtain ⟨next,hnext⟩ := least?_some h
        have nextEdge : Edge (targetTree G root) v next :=
          mem_filter.mpr ⟨(mem_filter.mp (least?_mem hnext)).2.1,hnext⟩
        obtain ⟨r,l⟩ := targetTree_edge nextEdge
        exact (ih _ (eq ▸ l) next rfl r).head nextEdge
  exact aux _ u rfl reachable

theorem targetTree_arborescence (G : Arcs V) (root : V) : InArborescence (targetTree G root) root := by
  constructor
  · have mono {u v : V} (r : Reach (targetTree G root) u v) : hops G v root ≤ hops G u root := by
      induction r with
      | refl => exact le_rfl
      | tail _ e ih => exact (targetTree_edge e).2.le.trans ih
    intro u v edge back
    exact (not_lt_of_ge (mono back)) (targetTree_edge edge).2
  · intro u v w vEdge wEdge
    exact Option.some.inj ((mem_filter.mp vEdge).2.symm.trans (mem_filter.mp wEdge).2)
  · intro e he
    have h : Reach G e.2 root := (targetTree_edge he).1
    exact ⟨targetTree_reach (h.head (targetTree_subset G root he)),targetTree_reach h⟩

omit [LinearOrder V] [Fintype V] in
private theorem empty_arborescence (root : V) : InArborescence ∅ root := by
  constructor <;> simp [IsDAG,Edge]

private def outTree (G : Arcs V) (root : V) : Arcs V :=
  reverseArcs (targetTree (reverseArcs G) root)

private theorem outTree_subset (G : Arcs V) (root : V) : outTree G root ⊆ G := by
  simpa [outTree] using reverseArcs_mono (targetTree_subset (reverseArcs G) root)

private theorem outTree_reach {G : Arcs V} {root u : V} (h : Reach G root u) :
    Reach (outTree G root) root u :=
  reach_reverseArcs.mpr (targetTree_reach (reach_reverseArcs.mpr h))

private theorem outTree_arborescence (G : Arcs V) (root : V) :
    InArborescence (reverseArcs (outTree G root)) root := by
  simpa [outTree] using targetTree_arborescence (reverseArcs G) root

/-- A set of demands served by two directed leg graphs around a common root. -/
structure JunctionPiece (Z : Arcs V) where
  root : V
  demands : Finset (V × V)
  inward : Arcs V
  outward : Arcs V
  inward_tree : InArborescence inward root
  outward_tree : InArborescence (reverseArcs outward) root
  inward_sub : inward ⊆ Z
  outward_sub : outward ⊆ Z
  served : ∀ d ∈ demands, Reach inward d.1 root ∧ Reach outward root d.2

def JunctionPiece.cost {Z : Arcs V} (piece : JunctionPiece Z) : ℕ :=
  piece.inward.card+piece.outward.card

def JunctionCover {Z : Arcs V} (pieces : List (JunctionPiece Z)) (P : Finset (V × V)) : Prop :=
  ∀ d ∈ P, ∃ piece ∈ pieces, d ∈ piece.demands

private def chosenLegs (Z : Arcs V) (d : V × V) : Arcs V :=
  pathArcs (routePath Z d.1 d.2)

private theorem chosenLegs_subset (Z : Arcs V) (d : V × V) : chosenLegs Z d ⊆ Z := by
  intro e he
  cases h : routePath Z d.1 d.2 with
  | none => simp [chosenLegs,pathArcs,h] at he
  | some path => exact (routePath_some h).1.mem (by simpa [chosenLegs,pathArcs,h] using he)

private theorem chosenLegs_reach {Z : Arcs V} {d : V × V} (reach : Reach Z d.1 d.2) :
    Reach (chosenLegs Z d) d.1 d.2 := by
  obtain ⟨l,hl⟩ := routePath_succeeds.mpr reach
  simpa [chosenLegs,pathArcs,hl] using (routePath_some hl).1.in_edges.reachable

private theorem chosenLegs_through {Z : Arcs V} {d e : V × V} (he : e ∈ chosenLegs Z d) :
    Reach Z d.1 e.1 ∧ Reach Z e.1 d.2 := by
  cases h : routePath Z d.1 d.2 with
  | none => simp [chosenLegs,pathArcs,h] at he
  | some path =>
    have w := (routePath_some h).1
    have m : e ∈ path := by simpa [chosenLegs,pathArcs,h] using he
    exact ⟨w.from_start m,(w.to_end m).head (w.mem m)⟩

private def lightJunction (Z : Arcs V) (d : V × V) (reachable : Reach Z d.1 d.2) :
    JunctionPiece Z where
  root := d.1
  demands := {d}
  inward := ∅
  outward := outTree (chosenLegs Z d) d.1
  inward_tree := empty_arborescence _
  outward_tree := outTree_arborescence _ _
  inward_sub := empty_subset _
  outward_sub := (outTree_subset _ _).trans (chosenLegs_subset Z d)
  served := by
    intro a ha
    obtain rfl := mem_singleton.mp ha
    exact ⟨.refl,outTree_reach (chosenLegs_reach reachable)⟩

private def heavyJunction (Z : Arcs V) (P : Finset (V × V)) (e : V × V) :
    JunctionPiece Z where
  root := e.1
  demands := P.filter fun d => e ∈ chosenLegs Z d
  inward := targetTree Z e.1
  outward := outTree Z e.1
  inward_tree := targetTree_arborescence _ _
  outward_tree := outTree_arborescence _ _
  inward_sub := targetTree_subset _ _
  outward_sub := outTree_subset _ _
  served := by
    intro d hd
    obtain ⟨before,after⟩ := chosenLegs_through (mem_filter.mp hd).2
    exact ⟨targetTree_reach before,outTree_reach after⟩

private theorem lightJunction_sum (Z : Arcs V) (P : Finset (V × V)) (k : ℕ)
    (light : ∀ e ∈ Z, (P.filter fun d => e ∈ chosenLegs Z d).card < k) :
    (∑ d ∈ P, (chosenLegs Z d).card) ≤ k*Z.card := by
  have left (d : V × V) : (chosenLegs Z d).card = ∑ e ∈ Z, if e ∈ chosenLegs Z d then 1 else 0 := by
    rw [← sum_filter]
    simp [filter_mem_eq_inter,inter_eq_right.mpr (chosenLegs_subset Z d)]
  have right (e : V × V) :
      (∑ d ∈ P, if e ∈ chosenLegs Z d then 1 else 0) = (P.filter fun d => e ∈ chosenLegs Z d).card := by
    rw [← sum_filter]
    simp
  calc
    _ = ∑ d ∈ P, ∑ e ∈ Z, if e ∈ chosenLegs Z d then 1 else 0 := sum_congr rfl fun d _ => left d
    _ = ∑ e ∈ Z, ∑ d ∈ P, if e ∈ chosenLegs Z d then 1 else 0 := sum_comm
    _ = ∑ e ∈ Z, (P.filter fun d => e ∈ chosenLegs Z d).card := sum_congr rfl fun e _ => right e
    _ ≤ ∑ _e ∈ Z, k := sum_le_sum fun e he => (light e he).le
    _ = _ := by simp [Nat.mul_comm]

private theorem lightJunction_cover (Z : Arcs V) (P : Finset (V × V))
    (reachable : ∀ d ∈ P, Reach Z d.1 d.2) :
    ∃ pieces : List (JunctionPiece Z), JunctionCover pieces P ∧
      (pieces.map JunctionPiece.cost).sum ≤ ∑ d ∈ P, (chosenLegs Z d).card := by
  classical
  let make (d : ↥P) := lightJunction Z d.1 (reachable d.1 d.2)
  let pieces := P.attach.toList.map make
  refine ⟨pieces,?_,?_⟩
  · intro d hd
    refine ⟨make ⟨d,hd⟩, List.mem_map_of_mem (by simp),?_⟩
    simp [make,lightJunction]
  · have sum_of_nodup (L : List ↥P) (hL : L.Nodup) :
        (L.map (fun d => (make d).cost)).sum = ∑ d ∈ L.toFinset, (make d).cost := by
      induction L with
      | nil => simp
      | cons d L ih =>
        obtain ⟨no,nd⟩ := List.nodup_cons.mp hL
        simp [ih nd, sum_insert (List.mem_toFinset.not.mpr no)]
    change ((P.attach.toList.map make).map JunctionPiece.cost).sum ≤ _
    rw [List.map_map]
    change (P.attach.toList.map (fun d => (make d).cost)).sum ≤ _
    rw [sum_of_nodup _ (nodup_toList _),toList_toFinset]
    calc
      _ ≤ ∑ d ∈ P.attach, (chosenLegs Z d.1).card := by
        apply sum_le_sum
        intro d _
        simp only [make,lightJunction,JunctionPiece.cost,card_empty,zero_add]
        exact card_le_card (outTree_subset _ _)
      _ = _ := sum_attach P (fun d => (chosenLegs Z d).card)

/-- The unweighted square-root routing comparison at any positive load cutoff.
The bound charges the legs separately even when their original arcs overlap. -/
theorem junctionCover_cutoff (Z : Arcs V) (P : Finset (V × V))
    (reachable : ∀ d ∈ P, Reach Z d.1 d.2) {k : ℕ} (hk : 0 < k) :
    ∃ pieces : List (JunctionPiece Z), JunctionCover pieces P ∧
      (pieces.map JunctionPiece.cost).sum ≤ (2*(P.card/k)+k)*Z.card := by
  classical
  induction P using Finset.strongInduction with
  | H P ih =>
    by_cases heavy : ∃ e ∈ Z, k ≤ (P.filter fun d => e ∈ chosenLegs Z d).card
    · obtain ⟨e,_he,hload⟩ := heavy
      let big := heavyJunction Z P e
      let small := P \ big.demands
      have bigSub : big.demands ⊆ P := filter_subset _ _
      have sumCard : small.card+big.demands.card = P.card := card_sdiff_add_card_eq_card bigSub
      have pos : 0 < big.demands.card := hk.trans_le hload
      have leftSub : small ⊂ P := by
        apply ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset,fun eq => ?_⟩
        rw [eq] at sumCard
        omega
      obtain ⟨pieces,cover,cost⟩ := ih small leftSub (fun d hd => reachable d (mem_sdiff.mp hd).1)
      refine ⟨big::pieces,?_,?_⟩
      · intro d hd
        by_cases hit : d ∈ big.demands
        · exact ⟨big,List.mem_cons_self,hit⟩
        · obtain ⟨piece,hpiece,hserved⟩ := cover d (mem_sdiff.mpr ⟨hd,hit⟩)
          exact ⟨piece,List.mem_cons_of_mem _ hpiece,hserved⟩
      · have quota : small.card/k+1 ≤ P.card/k := by
          apply (Nat.le_div_iff_mul_le hk).mpr
          rw [Nat.add_mul,Nat.one_mul]
          have := Nat.div_mul_le_self small.card k
          change k ≤ big.demands.card at hload
          omega
        simp only [List.map_cons,List.sum_cons]
        have charge : big.cost ≤ 2*Z.card := by
          unfold JunctionPiece.cost
          rw [two_mul]
          exact Nat.add_le_add (card_le_card big.inward_sub) (card_le_card big.outward_sub)
        calc
          _ ≤ 2*Z.card+(2*(small.card/k)+k)*Z.card := Nat.add_le_add charge cost
          _ = (2*(small.card/k+1)+k)*Z.card := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · have light : ∀ e ∈ Z, (P.filter fun d => e ∈ chosenLegs Z d).card < k :=
        fun e he => lt_of_not_ge (fun hl => heavy ⟨e,he,hl⟩)
      obtain ⟨pieces,cover,cost⟩ := lightJunction_cover Z P reachable
      refine ⟨pieces,cover,?_⟩
      exact cost.trans ((lightJunction_sum Z P k light).trans (Nat.mul_le_mul_right _ (by omega)))

/-- The finite square-root bound for the rooted routing comparison. -/
theorem junctionCover_sqrt (Z : Arcs V) (P : Finset (V × V))
    (reachable : ∀ d ∈ P, Reach Z d.1 d.2) :
    ∃ pieces : List (JunctionPiece Z), JunctionCover pieces P ∧
      (pieces.map JunctionPiece.cost).sum ≤ 3*(Nat.sqrt P.card+1)*Z.card := by
  let k := Nat.sqrt P.card+1
  have kpos : 0 < k := by simp [k]
  obtain ⟨pieces,cover,cost⟩ := junctionCover_cutoff Z P reachable kpos
  have h : P.card/k ≤ k := (Nat.div_le_iff_le_mul kpos).mpr (by
    have h := (Nat.lt_succ_sqrt' P.card).le
    change P.card ≤ k^2 at h
    rw [pow_two] at h
    omega)
  exact ⟨pieces,cover,cost.trans (Nat.mul_le_mul_right _ (by omega))⟩

end OnlineReachabilityPreservers
