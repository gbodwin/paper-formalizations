import OnlineReachabilityPreservers.SccListWork
import OnlineReachabilityPreservers.AlgorithmSearchWork
import OnlineReachabilityPreservers.OfflineListWork

/-! List-backed SCC representatives, internal connectors, and exact lifted runs. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

omit [Fintype V] in
private def projectionRowsWithChecks (table arcs : List (V × V)) :
    List ((V × V) × (V × V)) × ℕ :=
  let projected := projectPairsWithChecks table arcs
  (arcs.zip projected.1,projected.2)

omit [Fintype V] in
private theorem projectionRowsWithChecks_spec (label : V → V) (keys : List V) (arcs : List (V × V))
    (enumerate : ∀ v : V, v ∈ keys) :
    let table := keys.map (fun v => (v,label v))
    let out := projectionRowsWithChecks table arcs
    out.1 = arcs.map (fun e => (e,(label e.1,label e.2))) ∧ out.2 ≤ arcs.length*(2*keys.length) := by
  obtain ⟨same, work⟩ := projectPairsWithChecks_spec label keys arcs enumerate
  refine ⟨?_,work⟩
  unfold projectionRowsWithChecks
  dsimp only
  rw [same]
  clear same work
  induction arcs with
  | nil => rfl
  | cons e es ih => simp [ih]

-- The original arc is the primary lexicographic key, and its projected arc is the secondary key.
private abbrev RepresentativeKey (V : Type*) := Lex (Lex (V × V) × Lex (V × V))

omit [Fintype V] in
private def representativeKey (a p : V × V) : RepresentativeKey V := toLex (toLex a,toLex p)

omit [Fintype V] in
private def representativeArc (row : RepresentativeKey V) : Lex (V × V) := (ofLex row).1

omit [Fintype V] in
private def representativeProjection (row : RepresentativeKey V) : V × V := ofLex (ofLex row).2

omit [Fintype V] in
private theorem representativeArc_mono : Monotone (representativeArc (V := V)) := by
  intro a b order
  rcases Prod.Lex.le_iff.mp order with left | ⟨same,_⟩
  · exact le_of_lt left
  · exact le_of_eq same

private theorem least?_map_image_of_monotone {A B : Type*} [LinearOrder A] [LinearOrder B]
    (S : Finset A) (f : A → B) (mono : Monotone f) :
    (least? S).map f = least? (S.image f) := by
  cases found : least? S with
  | none => simp [least?_eq_none.mp found, least?]
  | some a =>
    obtain ⟨b, least⟩ := least?_some (show (S.image f).Nonempty from ⟨f a, mem_image_of_mem _ (least?_mem found)⟩)
    rw [least]
    apply congrArg some
    apply le_antisymm
    · obtain ⟨c, member, rfl⟩ := mem_image.mp (least?_mem least)
      exact mono (least?_le found member)
    · exact least?_le least (mem_image_of_mem _ (least?_mem found))

omit [Fintype V] in
private def representativeKeys (rows : List ((V × V) × (V × V))) : List (RepresentativeKey V) :=
  rows.map (fun row => representativeKey row.1 row.2)

omit [Fintype V] in
private def representativeListWithChecks (rows : List (RepresentativeKey V)) (key : V × V) :
    Option (V × V) × ℕ :=
  let least := leastWhereWithChecks (fun row => (decide (representativeProjection row = key), 1)) rows
  (least.1.map (fun row => ofLex (representativeArc row)), least.2)

private theorem representativeListWithChecks_spec (arcs : List (V × V)) (key : V × V) :
    let rows := representativeKeys (arcs.map (fun a => (a,projectDemand arcs.toFinset a)))
    let out := representativeListWithChecks rows key
    out.1.toList.toFinset = liftOne arcs.toFinset key ∧ out.2 ≤ arcs.length*2 := by
  let rows := representativeKeys (arcs.map (fun a => (a,projectDemand arcs.toFinset a)))
  let P := fun row => representativeProjection row = key
  obtain ⟨minimum, charge⟩ := leastWhereWithChecks_spec (fun row => (decide (P row),1)) P rows 1
    (fun _ _ => rfl) (fun _ _ => le_rfl)
  have identified : (rows.toFinset.filter P).image representativeArc = crossingCandidates arcs.toFinset key := by
    ext arc
    simp only [mem_image, mem_filter, List.mem_toFinset, rows, P, representativeKeys, List.mem_map,
      crossingCandidates]
    constructor
    · rintro ⟨row,⟨⟨pair,⟨a,ha,rfl⟩,rfl⟩, hkey⟩,rfl⟩
      exact ⟨a,⟨ha,hkey⟩,rfl⟩
    · rintro ⟨a,⟨ha,hkey⟩,rfl⟩
      exact ⟨representativeKey a (projectDemand arcs.toFinset a),⟨⟨_,⟨a,ha,rfl⟩,rfl⟩,hkey⟩,rfl⟩
  refine ⟨?_, ?_⟩
  · change (Option.map (fun row => ofLex (representativeArc row))
      (leastWhereWithChecks (fun row => (decide (P row),1)) rows).1).toList.toFinset = _
    rw [minimum]
    have composed : (fun row : RepresentativeKey V => ofLex (representativeArc row)) =
        ofLex ∘ representativeArc := rfl
    rw [composed, ← Option.map_map, least?_map_image_of_monotone _ _ representativeArc_mono, identified]
    unfold liftOne
    cases least? (crossingCandidates arcs.toFinset key) <;> rfl
  · change (leastWhereWithChecks (fun row => (decide (P row),1)) rows).2 ≤ _
    simpa only [rows, representativeKeys, List.length_map] using charge

/-- Lift the selected condensed arcs from a cached list of projected original arcs. -/
def liftedArcsListWithChecks (table arcs selected : List (V × V)) : List (V × V) × ℕ :=
  let projected := projectionRowsWithChecks table arcs
  let rows := representativeKeys projected.1
  let representatives := mapListWithChecks (representativeListWithChecks rows) selected
  (representatives.1.flatMap Option.toList, projected.2+representatives.2)

theorem liftedArcsListWithChecks_spec (keys : List V) (arcs selected : List (V × V))
    (enumerate : ∀ v : V, v ∈ keys) :
    let table := keys.map (fun v => (v,componentLabel arcs.toFinset v))
    let out := liftedArcsListWithChecks table arcs selected
    out.1.toFinset = liftedArcs arcs.toFinset selected.toFinset ∧
    out.2 ≤ arcs.length*(2*keys.length) + selected.length*(2*arcs.length) := by
  let label := componentLabel arcs.toFinset
  let table := keys.map (fun v => (v,label v))
  let rows := representativeKeys (arcs.map (fun a => (a,projectDemand arcs.toFinset a)))
  let find := representativeListWithChecks rows
  let representatives := mapListWithChecks find selected
  obtain ⟨projected, prep⟩ := projectionRowsWithChecks_spec label keys arcs enumerate
  change (projectionRowsWithChecks table arcs).1 =
    arcs.map (fun a => (a,projectDemand arcs.toFinset a)) at projected
  obtain ⟨same, scans⟩ := mapListWithChecks_spec find (fun key => (find key).1)
    selected (arcs.length*2) (fun _ _ => rfl)
    (fun key _ => (representativeListWithChecks_spec arcs key).2)
  unfold liftedArcsListWithChecks
  dsimp only
  rw [projected]
  refine ⟨?_, ?_⟩
  · change (representatives.1.flatMap Option.toList).toFinset = _
    have eq : representatives.1 = selected.map (fun key => (find key).1) := same
    rw [eq]
    ext e
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map, liftedArcs, mem_biUnion]
    constructor
    · rintro ⟨option,⟨key,hkey,rfl⟩,h⟩
      have spec := (representativeListWithChecks_spec arcs key).1
      exact ⟨key,hkey,by rw [← spec]; exact List.mem_toFinset.mpr h⟩
    · rintro ⟨key,hkey,h⟩
      have spec := (representativeListWithChecks_spec arcs key).1
      exact ⟨(find key).1,⟨key,hkey,rfl⟩,List.mem_toFinset.mp (spec.symm ▸ h)⟩
  · exact Nat.add_le_add prep (by simpa only [Nat.mul_comm 2] using scans)


private def hopsListWithChecks (arcs : List (V × V)) (s t : V) : ℕ × ℕ :=
  let n := Fintype.card V
  let least := leastWhereWithChecks (reachTestListWithChecks arcs s t) (List.range (n+1))
  (least.1.getD (n+1),least.2)

private theorem hopsListWithChecks_spec (arcs : List (V × V)) (s t : V) :
    let n := Fintype.card V
    let out := hopsListWithChecks arcs s t
    out.1 = hops arcs.toFinset s t ∧ out.2 ≤ (n+1)*(n*(arcs.length*(2*n))+n+1) := by
  let n := Fintype.card V
  let P := fun k => s ∈ reachIn arcs.toFinset t k
  obtain ⟨least, charge⟩ := leastWhereWithChecks_spec (reachTestListWithChecks arcs s t) P
    (List.range (n+1)) (n*(arcs.length*(2*n))+n)
    (fun k _ => (reachTestListWithChecks_spec arcs s t k).1)
    (fun k incl => (reachTestListWithChecks_spec arcs s t k).2.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (List.mem_range.mp incl))) n))
  have candidates : (List.range (n+1)).toFinset = range (n+1) := by
    ext k
    simp
  change (leastWhereWithChecks _ _).1.getD (n+1) = hops arcs.toFinset s t ∧
    (leastWhereWithChecks _ _).2 ≤ _
  rw [least, candidates]
  exact ⟨rfl, by simpa only [List.length_range] using charge⟩

/-- Comparison cap for an internal connector at one vertex. -/
def towardRootListBudget (n m : ℕ) : ℕ :=
  1+(n+1)*(n*(m*(2*n))+n+1)+n*(m*(2*n))+n*(m+1)

omit [Fintype V] in
private def towardRootListWithWork (findHops : V → V → ℕ × ℕ)
    (findReach : V → ℕ → List V × ℕ) (pick : V → List V → Option V × ℕ)
    (rootCharge edgeCharge : ℕ) (row : V × V) : Option (V × V) × ℕ :=
  let (s,t) := row
  if s = t then (none,rootCharge)
  else
    let hops := findHops s t
    let reached := findReach t (hops.1-1)
    let next := pick s reached.1
    (next.1.map (s,·),edgeCharge+hops.2+reached.2+next.2)

private def towardRootListWithChecks (arcs : List (V × V)) (row : V × V) : Option (V × V) × ℕ :=
  towardRootListWithWork (hopsListWithChecks arcs) (reachInListWithChecks arcs)
    (leastSuccessorWithChecks arcs) 1 1 row

private theorem towardRootListWithChecks_spec (arcs : List (V × V)) (s : V) :
    let t := componentLabel arcs.toFinset s
    let out := towardRootListWithChecks arcs (s,t)
    out.1.toList.toFinset = towardRoot arcs.toFinset s ∧
      out.2 ≤ towardRootListBudget (Fintype.card V) arcs.length := by
  let t := componentLabel arcs.toFinset s
  let n := Fintype.card V
  change (towardRootListWithChecks arcs (s,t)).1.toList.toFinset = towardRoot arcs.toFinset s ∧
    (towardRootListWithChecks arcs (s,t)).2 ≤ towardRootListBudget n arcs.length
  by_cases same : s = t
  · have empty : towardRoot arcs.toFinset s = ∅ := by
      unfold towardRoot
      exact ite_eq_left same
    have root : towardRootListWithChecks arcs (s,t) = (none,1) := by
      unfold towardRootListWithChecks
      exact ite_eq_left same
    rw [empty,root]
    refine ⟨rfl,?_⟩
    unfold towardRootListBudget
    omega
  · let depth := hopsListWithChecks arcs s t
    obtain ⟨hits, hopWork⟩ := hopsListWithChecks_spec arcs s t
    have depthEq : depth.1 = hops arcs.toFinset s t := hits
    have limit : depth.1 - 1 ≤ n := by
      rw [depthEq]
      exact (Nat.sub_le _ _).trans (hops_spec (componentLabel_same s).1).1
    let reach := reachInListWithChecks arcs t (depth.1-1)
    obtain ⟨distinct, supports, reachWork⟩ := reachInListWithChecks_spec arcs t (depth.1-1)
    have nBound : reach.1.length ≤ n := by
      rw [← List.toFinset_card_of_nodup distinct]
      exact card_le_univ _
    obtain ⟨select, tests⟩ := leastSuccessorWithChecks_spec arcs s reach.1
    have chosen : (leastSuccessorWithChecks arcs s reach.1).1 =
        least? ((reachIn arcs.toFinset t (hops arcs.toFinset s t-1)).filter (Edge arcs.toFinset s)) := by
      rw [select, supports, depthEq]
    simp only [towardRootListWithChecks, towardRootListWithWork, same, ↓reduceIte]
    change (Option.map (s,·) (leastSuccessorWithChecks arcs s reach.1).1).toList.toFinset =
      towardRoot arcs.toFinset s ∧ 1+depth.2+reach.2+(leastSuccessorWithChecks arcs s reach.1).2 ≤ _
    refine ⟨?_, ?_⟩
    · rw [chosen]
      unfold towardRoot
      change _ = if s = t then ∅ else _
      rw [ite_eq_right same]
      cases least? ((reachIn arcs.toFinset t (hops arcs.toFinset s t-1)).filter
        (Edge arcs.toFinset s)) <;> rfl
    · exact Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add_left hopWork 1)
          (reachWork.trans (Nat.mul_le_mul_right _ limit)))
        (tests.trans (Nat.mul_le_mul_right _ nBound))

private def inTreesListWithChecks (arcs table : List (V × V)) : List (V × V) × ℕ :=
  let out := mapListWithChecks (towardRootListWithChecks arcs) table
  (out.1.flatMap Option.toList,out.2)

private theorem inTreesListWithChecks_spec (arcs : List (V × V)) (vertices : List V)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let labels := vertices.map (fun v => (v,componentLabel arcs.toFinset v))
    let out := inTreesListWithChecks arcs labels
    out.1.toFinset = inTrees arcs.toFinset ∧
      out.2 ≤ vertices.length*towardRootListBudget (Fintype.card V) arcs.length := by
  let row := fun v => (v,componentLabel arcs.toFinset v)
  let labels := vertices.map row
  let f := towardRootListWithChecks arcs
  obtain ⟨same, work⟩ := mapListWithChecks_spec f (fun r => (f r).1)
    labels (towardRootListBudget (Fintype.card V) arcs.length) (fun _ _ => rfl) (by
      intro r member
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp member
      exact (towardRootListWithChecks_spec arcs v).2)
  have bound : (inTreesListWithChecks arcs labels).2 ≤
      vertices.length*towardRootListBudget (Fintype.card V) arcs.length := by
    change (mapListWithChecks f labels).2 ≤ _
    simpa only [labels, List.length_map] using work
  refine ⟨?_,bound⟩
  change ((mapListWithChecks f labels).1.flatMap Option.toList).toFinset = _
  rw [same]
  ext e
  simp only [List.mem_toFinset, List.mem_flatMap, labels, List.map_map, List.mem_map, inTrees, mem_biUnion,
    mem_univ, true_and]
  constructor
  · rintro ⟨opt,⟨v,_,rfl⟩,he⟩
    exact ⟨v,(towardRootListWithChecks_spec arcs v).1 ▸ List.mem_toFinset.mpr he⟩
  · rintro ⟨v,he⟩
    exact ⟨_,⟨v,enumerate v,rfl⟩,List.mem_toFinset.mp ((towardRootListWithChecks_spec arcs v).1.symm ▸ he)⟩

/-- Reuse the common label table to choose an in- and an out-tree for every SCC. -/
def connectorsListWithChecks (arcs table : List (V × V)) : List (V × V) × ℕ :=
  let inward := inTreesListWithChecks arcs table
  let outward := inTreesListWithChecks (arcs.map Prod.swap) table
  (inward.1 ++ outward.1.map Prod.swap,inward.2+outward.2)

theorem connectorsListWithChecks_spec (arcs : List (V × V)) (vertices : List V)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let labels := vertices.map (fun v => (v,componentLabel arcs.toFinset v))
    let out := connectorsListWithChecks arcs labels
    out.1.toFinset = connectors arcs.toFinset ∧
      out.2 ≤ 2*vertices.length*towardRootListBudget (Fintype.card V) arcs.length := by
  let labels := vertices.map (fun v => (v,componentLabel arcs.toFinset v))
  let inward := inTreesListWithChecks arcs labels
  let outward := inTreesListWithChecks (arcs.map Prod.swap) labels
  have sameTable : (vertices.map (fun v => (v,componentLabel (reverseArcs arcs.toFinset) v))) = labels := by
    simp only [componentLabel_reverse, labels]
  obtain ⟨inArcs,inWork⟩ := inTreesListWithChecks_spec arcs vertices enumerate
  obtain ⟨outArcs,outWork⟩ := inTreesListWithChecks_spec (arcs.map Prod.swap) vertices enumerate
  simp only [reverseArcList_toFinset, List.length_map] at outArcs outWork
  rw [sameTable] at outArcs outWork
  change (inward.1 ++ outward.1.map Prod.swap).toFinset = connectors arcs.toFinset ∧
    inward.2+outward.2 ≤ _
  rw [List.toFinset_append, reverseArcList_toFinset, inArcs, outArcs]
  exact ⟨rfl, (Nat.add_le_add inWork outWork).trans_eq (by ring)⟩

omit [LinearOrder V] [Fintype V] in
private theorem optionalOutputs_length {A B : Type*} (step : A → B × ℕ)
    (keep : B → Option (V × V)) (rows : List A) :
    ((mapListWithChecks step rows).1.flatMap (fun x => (keep x).toList)).length ≤ rows.length := by
  induction rows with
  | nil => simp [mapListWithChecks]
  | cons a as ih =>
    simp only [mapListWithChecks, List.flatMap_cons, List.length_append, List.length_cons]
    cases present : keep (step a).1 with
    | none => simpa only [Option.toList_none, List.length_nil, zero_add] using
        ih.trans (Nat.le_succ _)
    | some e => simpa only [Option.toList_some, List.length_singleton, Nat.add_comm 1] using
        Nat.succ_le_succ ih

private theorem connectorsListWithChecks_length (arcs table : List (V × V)) :
    (connectorsListWithChecks arcs table).1.length ≤ 2*table.length := by
  have inward := optionalOutputs_length (towardRootListWithChecks arcs) id table
  have outward := optionalOutputs_length (towardRootListWithChecks (arcs.map Prod.swap)) id table
  unfold connectorsListWithChecks inTreesListWithChecks
  simp only [List.length_append, List.length_map, two_mul, id_eq] at *
  exact Nat.add_le_add inward outward

omit [Fintype V] in
private theorem liftedArcsListWithChecks_length (table arcs selected : List (V × V)) :
    (liftedArcsListWithChecks table arcs selected).1.length ≤ selected.length :=
  optionalOutputs_length (representativeListWithChecks
    (representativeKeys (projectionRowsWithChecks table arcs).1)) id selected

/-- Key-comparison allowance for SCC preprocessing, requests and the original-arc lift. -/
def liftCoreListBudget (n m p : ℕ) : ℕ :=
  condensationListBudget n m + p*(2*n) + 2*n*towardRootListBudget n m +
    m*(2*n) + m*(2*m) + (2*n+m)*n^2

/-- Evaluate a list-backed condensed algorithm and lift its edges. -/
def liftCoreListWithChecks
    (run : List (V × V) → List (V × V) → List (V × V) × ℕ)
    (arcs : List (V × V)) (vertices : List V) :
    List (V × V) → List (V × V) × ℕ
  | [] => ([],0)
  | d::rest =>
    let prepared := prepareCondensationWithChecks arcs vertices
    let table := prepared.1.1
    let projected := projectPairsWithChecks table (d::rest)
    let selected := run prepared.1.2 projected.1
    let internal := connectorsListWithChecks arcs table
    let cross := liftedArcsListWithChecks table arcs selected.1
    let unique := insertListWithChecks (internal.1 ++ cross.1) []
    (unique.1,prepared.2+projected.2+selected.2+internal.2+cross.2+unique.2)

theorem liftCoreListWithChecks_spec
    (run : List (V × V) → List (V × V) → List (V × V) × ℕ)
    (plain : Arcs V → List (V × V) → Arcs V)
    (budget : ℕ → ℕ → ℕ → ℕ)
    (same : ∀ K T : List (V × V), K.Nodup →
      (run K T).1.Nodup ∧ (run K T).1.toFinset = plain K.toFinset T ∧
      (run K T).2 ≤ budget (Fintype.card V) K.length T.length)
    (sub : ∀ K T, plain K T ⊆ K)
    (mono : ∀ n p, Monotone fun m => budget n m p)
    (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := arcs.length
    let out := liftCoreListWithChecks run arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = liftedRun plain arcs.toFinset demands ∧
      out.2 ≤ liftCoreListBudget n m demands.length + budget n m demands.length := by
  cases demands with
  | nil => simp [liftCoreListWithChecks, liftedRun]
  | cons req rest =>
    let demands := req::rest
    let n := Fintype.card V
    let m := arcs.length
    let prepared := prepareCondensationWithChecks arcs vertices
    let table := prepared.1.1
    let projected := projectPairsWithChecks table demands
    let selected := run prepared.1.2 projected.1
    let internal := connectorsListWithChecks arcs table
    let cross := liftedArcsListWithChecks table arcs selected.1
    let unique := insertListWithChecks (internal.1 ++ cross.1) []
    have cover : vertices.toFinset = univ := by ext v; simp [enumerate v]
    have count : vertices.length = n := by
      rw [← List.toFinset_card_of_nodup simple, cover, card_univ]
    obtain ⟨labels,graphSimple,graph,graphSize,prepCost⟩ := prepareCondensationWithChecks_spec arcs vertices simple enumerate
    have tableEq : table = vertices.map (fun v => (v,componentLabel arcs.toFinset v)) := labels
    obtain ⟨keys,queryCost⟩ := projectPairsWithChecks_spec (componentLabel arcs.toFinset) vertices demands enumerate
    have trace : projected.1 = demands.map (projectDemand arcs.toFinset) := by
      unfold projected
      rw [tableEq]
      exact keys
    have projectedCost : projected.2 ≤ demands.length*(2*n) := by
      unfold projected
      rw [tableEq]
      simpa only [count] using queryCost
    have projectedLength : projected.1.length = demands.length := by rw [trace, List.length_map]
    obtain ⟨selectedSimple, selectedSet,selectCost⟩ :=
      same prepared.1.2 projected.1 graphSimple
    have graphEq : prepared.1.2.toFinset = condensation arcs.toFinset := graph
    have selectedEq : selected.1.toFinset =
        plain (condensation arcs.toFinset) (demands.map (projectDemand arcs.toFinset)) := by
      unfold selected
      rw [selectedSet, graphEq, trace]
    have selectedCap : selected.1.length ≤ m := by
      rw [← List.toFinset_card_of_nodup selectedSimple, selectedEq]
      have arcCap : (condensation arcs.toFinset).card ≤ arcs.toFinset.card :=
        card_image_le.trans (card_le_card (filter_subset _ _))
      exact (card_le_card (sub _ _)).trans
        (arcCap.trans (List.toFinset_card_le _))
    have tableCount : table.length = n := by rw [tableEq, List.length_map, count]
    have selectCap : selected.2 ≤ budget n m demands.length := by
      rw [← projectedLength]
      exact selectCost.trans (mono _ _ graphSize)
    obtain ⟨intSet,intCost⟩ := connectorsListWithChecks_spec arcs vertices enumerate
    obtain ⟨liftSet,liftCost⟩ := liftedArcsListWithChecks_spec vertices arcs selected.1 enumerate
    have intExact : internal.1.toFinset = connectors arcs.toFinset := by
      unfold internal
      rw [tableEq]
      exact intSet
    have intCap : internal.2 ≤ 2*n*towardRootListBudget n m := by
      unfold internal
      rw [tableEq]
      simpa only [count] using intCost
    have crossExact : cross.1.toFinset = liftedArcs arcs.toFinset selected.1.toFinset := by
      unfold cross
      rw [tableEq]
      exact liftSet
    have crossCap : cross.2 ≤ m*(2*n) + m*(2*m) := by
      unfold cross
      rw [tableEq]
      exact liftCost.trans (by rw [count]; gcongr)
    obtain ⟨uniqueSimple,uniqueSet,uniqueCost⟩ :=
      insertListWithChecks_spec (internal.1 ++ cross.1) [] (by simp)
    have uniqueCap : unique.2 ≤ (2*n+m)*n^2 := by
      have intSize := connectorsListWithChecks_length arcs table
      have crossSize := liftedArcsListWithChecks_length table arcs selected.1
      change internal.1.length ≤ 2*table.length at intSize
      change cross.1.length ≤ selected.1.length at crossSize
      rw [tableCount] at intSize
      have sumLength : (internal.1 ++ cross.1).length ≤ 2*n+m := by
        rw [List.length_append]
        exact Nat.add_le_add intSize (crossSize.trans selectedCap)
      have work := uniqueCost.trans (Nat.mul_le_mul_right _ sumLength)
      simpa only [Fintype.card_prod, ← pow_two] using work
    refine ⟨uniqueSimple,?_,?_⟩
    · change unique.1.toFinset = connectors arcs.toFinset ∪
        liftedArcs arcs.toFinset (plain (condensation arcs.toFinset)
          (demands.map (projectDemand arcs.toFinset)))
      rw [uniqueSet, List.toFinset_nil, empty_union, List.toFinset_append, intExact, crossExact, selectedEq]
    · change prepared.2+projected.2+selected.2+internal.2+cross.2+unique.2 ≤ liftCoreListBudget n m _ + _
      have prepCap : prepared.2 ≤ condensationListBudget n m := prepCost
      have throughCore := Nat.add_le_add (Nat.add_le_add prepCap projectedCost) selectCap
      exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add throughCore intCap) crossCap) uniqueCap).trans_eq
        (by unfold liftCoreListBudget; ring)

/-- The comparison budget for the general-digraph forward run. -/
def sinkPreserverListBudget (n m p : ℕ) : ℕ :=
  liftCoreListBudget n m p + p*forwardStepListBudget n m

/-- Evaluate the ordinary forward preserver through SCC preprocessing and the original lift. -/
def sinkPreserverListWithChecks (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) : List (V × V) × ℕ :=
  liftCoreListWithChecks (fun K T => forwardRunListWithChecks K T []) arcs vertices demands

theorem sinkPreserverListWithChecks_spec (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let out := sinkPreserverListWithChecks arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = sinkPreserver arcs.toFinset demands ∧
      out.2 ≤ sinkPreserverListBudget (Fintype.card V) arcs.length demands.length :=
  liftCoreListWithChecks_spec _ forwardRun (fun n m p => p*forwardStepListBudget n m)
    (fun K T _ => forwardRunListWithChecks_spec K T [] (by simp))
    (fun _ _ => forwardRunFrom_subset (empty_subset _) _)
    (fun n p m k small => by dsimp only [forwardStepListBudget]; gcongr) arcs vertices demands simple enumerate

/-- Evaluate the source-restricted rule by reversing the lists and using the sink rule. -/
def sourcePreserverListWithChecks (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) : List (V × V) × ℕ :=
  let out := sinkPreserverListWithChecks (arcs.map Prod.swap) vertices (demands.map Prod.swap)
  (out.1.map Prod.swap,out.2)

theorem sourcePreserverListWithChecks_spec (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let out := sourcePreserverListWithChecks arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = sourcePreserver arcs.toFinset demands ∧
      out.2 ≤ sinkPreserverListBudget (Fintype.card V) arcs.length demands.length := by
  obtain ⟨distinct, same, work⟩ :=
    sinkPreserverListWithChecks_spec (arcs.map Prod.swap) vertices (demands.map Prod.swap) simple enumerate
  refine ⟨distinct.map Prod.swap_injective,?_,?_⟩
  · unfold sourcePreserverListWithChecks sourcePreserver
    simp only [reverseArcList_toFinset, same]
  · simpa only [sourcePreserverListWithChecks, List.length_map] using work

omit [Fintype V] in
private theorem preserverListWithChecks_prefixReplay (evaluate : List (V × V) → List (V × V) × ℕ)
    (plain : List (V × V) → Arcs V) (n m : ℕ) (demands : List (V × V))
    (spec : ∀ P, (evaluate P).1.toFinset = plain P ∧
      (evaluate P).2 ≤ sinkPreserverListBudget n m P.length) :
    let replay := prefixSearchReplay evaluate demands
    replay.1.map List.toFinset = demands.inits.map plain ∧
      replay.2 ≤ (demands.length+1)*sinkPreserverListBudget n m demands.length := by
  let out := fun P => ((evaluate P).1.toFinset,(evaluate P).2)
  have checked := prefixSearchReplay_spec out plain (sinkPreserverListBudget n m) demands
    (fun P => (spec P).1) (fun P early => (spec P).2.trans (by
      unfold sinkPreserverListBudget liftCoreListBudget
      gcongr <;> exact early.length_le))
  simpa only [prefixSearchReplay, List.map_map, out, Function.comp_def] using checked

/-- Recompute the sink-preserver output for each revealed prefix within
one polynomial budget for total key comparisons. -/
theorem sinkPreserverListWithChecks_prefixReplay (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let replay := prefixSearchReplay (sinkPreserverListWithChecks arcs vertices) demands
    replay.1.map List.toFinset = demands.inits.map (sinkPreserver arcs.toFinset) ∧
      replay.2 ≤ (demands.length+1)*sinkPreserverListBudget (Fintype.card V) arcs.length demands.length :=
  preserverListWithChecks_prefixReplay _ _ _ _ demands
    (fun P => (sinkPreserverListWithChecks_spec arcs vertices P simple enumerate).2)

/-- The corresponding prefix replay and total comparison budget for the source rule. -/
theorem sourcePreserverListWithChecks_prefixReplay (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let replay := prefixSearchReplay (sourcePreserverListWithChecks arcs vertices) demands
    replay.1.map List.toFinset = demands.inits.map (sourcePreserver arcs.toFinset) ∧
      replay.2 ≤ (demands.length+1)*sinkPreserverListBudget (Fintype.card V) arcs.length demands.length :=
  preserverListWithChecks_prefixReplay _ _ _ _ demands
    (fun P => (sourcePreserverListWithChecks_spec arcs vertices P simple enumerate).2)

private def offlineCoreListBudget (n m p : ℕ) : ℕ := m^2+m*pruneStepListBudget n m p

private theorem offlinePruneListWithChecks_polynomial (arcs demands : List (V × V)) (simple : arcs.Nodup) :
    let out := offlinePruneListWithChecks arcs demands
    out.1.Nodup ∧ out.1.toFinset = offlinePrune arcs.toFinset demands ∧
      out.2 ≤ offlineCoreListBudget (Fintype.card V) arcs.length demands.length := by
  obtain ⟨nodup,same,work⟩ := offlinePruneListWithChecks_spec arcs demands simple
  have logBound : arcs.length.size ≤ arcs.length := Nat.size_le.mpr Nat.lt_two_pow_self
  refine ⟨nodup,same,work.trans ?_⟩
  unfold offlineCoreListBudget
  rw [pow_two]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ logBound) _

/-- The comparison allowance for exact greedy offline pruning on a general graph. -/
def offlinePreserverListBudget (n m p : ℕ) : ℕ :=
  liftCoreListBudget n m p + offlineCoreListBudget n m p

/-- Evaluate the ordinary offline preserver with its original pruning order and SCC lift. -/
def offlinePreserverListWithChecks (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) : List (V × V) × ℕ :=
  liftCoreListWithChecks offlinePruneListWithChecks arcs vertices demands

theorem offlinePreserverListWithChecks_spec (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let out := offlinePreserverListWithChecks arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = offlinePreserver arcs.toFinset demands ∧
      out.2 ≤ offlinePreserverListBudget (Fintype.card V) arcs.length demands.length :=
  liftCoreListWithChecks_spec _ offlinePrune offlineCoreListBudget
    offlinePruneListWithChecks_polynomial (fun K T => (offlinePrune_spec K T).1)
    (fun n p m k small => by dsimp only [offlineCoreListBudget, pruneStepListBudget, servesListBudget]; gcongr)
    arcs vertices demands simple enumerate

/-- Find the first reverse-search depth that reaches the source, with a list tally. -/
def hopsListWithWordWork (arcs : List (V × V)) (s t : V) (depth : ℕ) : ℕ × ℕ :=
  let choices := List.range (depth+1)
  let least := leastWhereWithChecks (reachTestListWithWordWork arcs s t) choices
  (least.1.getD (depth+1), least.2+14*(depth+1)+5)

def hopsListWordBudget (n m : ℕ) : ℕ := (n+1)*(reachInListWordBudget n m+2*n+20)+5

theorem hopsListWithWordWork_spec (arcs : List (V × V)) (s t : V) :
    let n := Fintype.card V
    let out := hopsListWithWordWork arcs s t n
    out.1 = hops arcs.toFinset s t ∧ out.2 ≤ hopsListWordBudget n arcs.length := by
  let n := Fintype.card V
  let P := fun k => s ∈ reachIn arcs.toFinset t k
  let cap := reachInListWordBudget n arcs.length+2*n+5
  obtain ⟨least, charge⟩ := leastWhereWithChecks_spec (reachTestListWithWordWork arcs s t) P
    (List.range (n+1)) cap
    (fun k _ => (reachTestListWithWordWork_spec arcs s t k).1)
    (fun k inside => (reachTestListWithWordWork_spec arcs s t k).2.trans (by
      have bound := Nat.le_of_lt_succ (List.mem_range.mp inside)
      dsimp only [cap,reachInListWordBudget]
      gcongr))
  have candidates : (List.range (n+1)).toFinset = range (n+1) := by ext k; simp
  refine ⟨?_,?_⟩
  · change (leastWhereWithChecks _ _).1.getD (n+1) = _
    rw [least,candidates]
    rfl
  · change (leastWhereWithChecks _ _).2 + 14*(n+1) + 5 ≤ _
    have work : (leastWhereWithChecks (reachTestListWithWordWork arcs s t) (List.range (n+1))).2 ≤ (n+1)*(cap+1) := by
      simpa only [List.length_range] using charge
    exact (Nat.add_le_add_right (Nat.add_le_add_right work _) _).trans_eq (by unfold hopsListWordBudget cap; ring)

omit [Fintype V] in
private def towardRootListWithWordWork (arcs : List (V × V)) (depth : ℕ) (row : V × V) : Option (V × V) × ℕ :=
  towardRootListWithWork (fun s t => hopsListWithWordWork arcs s t depth)
    (reachInListWithWordWork arcs) (leastSuccessorWithWordWork arcs) 5 8 row

private def towardRootWordBudget (n m : ℕ) : ℕ :=
  8+hopsListWordBudget n m+reachInListWordBudget n m+(1+n*(2*m+10))

private theorem towardRootListWithWordWork_spec (arcs : List (V × V)) (s : V) :
    let t := componentLabel arcs.toFinset s
    let n := Fintype.card V
    let out := towardRootListWithWordWork arcs n (s,t)
    out.1.toList.toFinset = towardRoot arcs.toFinset s ∧ out.2 ≤ towardRootWordBudget n arcs.length := by
  let t := componentLabel arcs.toFinset s
  let n := Fintype.card V
  change (towardRootListWithWordWork arcs n (s,t)).1.toList.toFinset = towardRoot arcs.toFinset s ∧
    (towardRootListWithWordWork arcs n (s,t)).2 ≤ _
  by_cases same : s = t
  · have root : towardRootListWithWordWork arcs n (s,t) = (none,5) := by
      unfold towardRootListWithWordWork
      exact ite_eq_left same
    have empty : towardRoot arcs.toFinset s = ∅ := by
      unfold towardRoot
      exact ite_eq_left same
    rw [root,empty]
    refine ⟨rfl,?_⟩
    unfold towardRootWordBudget
    omega
  · let depth := hopsListWithWordWork arcs s t n
    let found := reachInListWithWordWork arcs t (depth.1-1)
    obtain ⟨hop, hopWork⟩ := hopsListWithWordWork_spec arcs s t
    have depthEq : depth.1 = hops arcs.toFinset s t := hop
    have limit : depth.1-1 ≤ n := by
      rw [depthEq]
      exact (Nat.sub_le _ _).trans (hops_spec (componentLabel_same s).1).1
    obtain ⟨simple, reached, work⟩ := reachInListWithWordWork_spec arcs t (depth.1-1)
    have foundSize : found.1.length ≤ n := by
      rw [← List.toFinset_card_of_nodup simple]
      exact card_le_univ _
    obtain ⟨picked, choice⟩ := leastSuccessorWithWordWork_spec arcs s found.1
    have result : (leastSuccessorWithWordWork arcs s found.1).1 =
        least? ((reachIn arcs.toFinset t (hops arcs.toFinset s t-1)).filter (Edge arcs.toFinset s)) := by
      rw [picked, show found.1.toFinset = _ from reached, depthEq]
    have workBound : found.2 ≤ reachInListWordBudget n arcs.length := work.trans (by
      change 2 + (depth.1-1)*(5+arcs.length*(14+4*n)) ≤ _
      unfold reachInListWordBudget
      gcongr)
    simp only [towardRootListWithWordWork,towardRootListWithWork,same,↓reduceIte]
    change (Option.map (s,·) (leastSuccessorWithWordWork arcs s found.1).1).toList.toFinset =
      towardRoot arcs.toFinset s ∧ 8+depth.2+found.2+(leastSuccessorWithWordWork arcs s found.1).2 ≤ _
    refine ⟨?_,?_⟩
    · rw [result]
      unfold towardRoot
      change _ = if s = t then ∅ else _
      rw [ite_eq_right same]
      cases least? ((reachIn arcs.toFinset t (hops arcs.toFinset s t-1)).filter (Edge arcs.toFinset s)) <;> rfl
    · exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hopWork _) workBound) (choice.trans (by gcongr))

omit [Fintype V] in
private def inTreesListWithWordWork (arcs table : List (V × V)) (depth : ℕ) : List (V × V) × ℕ :=
  let out := mapListWithChecks (towardRootListWithWordWork arcs depth) table
  (out.1.flatMap Option.toList,out.2+12*table.length+5)

private theorem inTreesListWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let table := vertices.map (fun v => (v,componentLabel arcs.toFinset v))
    let out := inTreesListWithWordWork arcs table n
    out.1.toFinset = inTrees arcs.toFinset ∧
      out.2 ≤ vertices.length*(towardRootWordBudget n arcs.length+12)+5 := by
  let row := fun v => (v,componentLabel arcs.toFinset v)
  let table := vertices.map row
  let evaluate := towardRootListWithWordWork arcs (Fintype.card V)
  obtain ⟨same, work⟩ := mapListWithChecks_spec evaluate (fun r => (evaluate r).1) table
    (towardRootWordBudget (Fintype.card V) arcs.length) (fun _ _ => rfl) (by
      intro r member
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp member
      exact (towardRootListWithWordWork_spec arcs v).2)
  refine ⟨?_,?_⟩
  · change ((mapListWithChecks evaluate table).1.flatMap Option.toList).toFinset = _
    rw [same]
    ext e
    simp only [List.mem_toFinset, List.mem_flatMap, table, List.map_map, List.mem_map, inTrees, mem_biUnion,
      mem_univ, true_and]
    constructor
    · rintro ⟨opt,⟨v,_,rfl⟩,he⟩
      exact ⟨v,(towardRootListWithWordWork_spec arcs v).1 ▸ List.mem_toFinset.mpr he⟩
    · rintro ⟨v,he⟩
      exact ⟨_,⟨v,enumerate v,rfl⟩,List.mem_toFinset.mp ((towardRootListWithWordWork_spec arcs v).1.symm ▸ he)⟩
  · change (mapListWithChecks evaluate table).2+12*table.length+5 ≤ _
    rw [show table.length = vertices.length from List.length_map _]
    have tally : (mapListWithChecks evaluate table).2 ≤ vertices.length*towardRootWordBudget (Fintype.card V) arcs.length := by
      simpa only [table,List.length_map] using work
    exact (Nat.add_le_add_right (Nat.add_le_add_right tally _) _).trans_eq (by ring)

omit [Fintype V] in
private def connectorsListWithWordWork (arcs table : List (V × V)) (depth : ℕ) : List (V × V) × ℕ :=
  let inward := inTreesListWithWordWork arcs table depth
  let outward := inTreesListWithWordWork (arcs.map Prod.swap) table depth
  (inward.1 ++ outward.1.map Prod.swap,inward.2+outward.2+6*arcs.length+12*table.length+5)

private def connectorsWordBudget (n m : ℕ) : ℕ := 2*n*(towardRootWordBudget n m+12)+6*m+12*n+15

omit [Fintype V] in
private theorem connectorsListWithWordWork_length (arcs table : List (V × V)) (depth : ℕ) :
    (connectorsListWithWordWork arcs table depth).1.length ≤ 2*table.length := by
  have inward := optionalOutputs_length (towardRootListWithWordWork arcs depth) id table
  have outward := optionalOutputs_length (towardRootListWithWordWork (arcs.map Prod.swap) depth) id table
  unfold connectorsListWithWordWork inTreesListWithWordWork
  simp only [List.length_append, List.length_map, two_mul, id_eq] at *
  exact Nat.add_le_add inward outward

private theorem connectorsListWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (complete : ∀ v : V, v ∈ vertices) (count : vertices.length = Fintype.card V) :
    let n := Fintype.card V
    let table := vertices.map (fun v => (v,componentLabel arcs.toFinset v))
    let out := connectorsListWithWordWork arcs table n
    out.1.toFinset = connectors arcs.toFinset ∧ out.2 ≤ connectorsWordBudget n arcs.length := by
  let n := Fintype.card V
  let table := vertices.map (fun v => (v,componentLabel arcs.toFinset v))
  let inward := inTreesListWithWordWork arcs table n
  let outward := inTreesListWithWordWork (arcs.map Prod.swap) table n
  have sameTable : (vertices.map (fun v => (v,componentLabel (reverseArcs arcs.toFinset) v))) = table := by
    simp only [componentLabel_reverse, table]
  obtain ⟨inSet,inWork⟩ := inTreesListWithWordWork_spec arcs vertices complete
  obtain ⟨outSet,outWork⟩ := inTreesListWithWordWork_spec (arcs.map Prod.swap) vertices complete
  simp only [reverseArcList_toFinset, List.length_map] at outSet outWork
  rw [sameTable] at outSet outWork
  change (inward.1 ++ outward.1.map Prod.swap).toFinset = _ ∧
    inward.2+outward.2+6*arcs.length+12*table.length+5 ≤ _
  rw [List.toFinset_append, reverseArcList_toFinset, inSet, outSet]
  refine ⟨rfl, ?_⟩
  have length : table.length = n := (List.length_map _).trans count
  have both : inward.2+outward.2 ≤ 2*(n*(towardRootWordBudget n arcs.length+12)+5) := by
    have sum := Nat.add_le_add inWork outWork
    simpa only [count, two_mul] using sum
  rw [length]
  exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right both _) _) _).trans_eq
    (by unfold connectorsWordBudget; ring)

/-- Source-level list work of the lift, excluding its quotient callback. -/
def liftCoreWordBudget (n m p : ℕ) : ℕ :=
  prepareCondensationWordBudget n m + 4*(p*(2*n))+16*p+2 + connectorsWordBudget n m +
    4*(m*(2*n)+m*(2*m))+36*m+5 + 2*((2*n+m)*n^2)+16*(2*n+m)+12 + (3*n+6)

omit [Fintype V] in
/-- An instrumented lift in the same list representation. The source-level
charges include projection, fixed-depth searches, both connector directions,
original representatives, and insertion of selected edges. -/
def liftCoreListWithWordWork
    (run : List (V × V) → ℕ → List (V × V) → List (V × V) × ℕ)
    (arcs : List (V × V)) (vertices : List V) : List (V × V) → List (V × V) × ℕ
  | [] => ([],1)
  | d::ds =>
    let prepared := prepareCondensationWithWordWork arcs vertices
    let table := prepared.1.1
    let depth := vertices.length
    let projected := projectPairsWithChecks table (d::ds)
    let selected := run prepared.1.2 depth projected.1
    let internal := connectorsListWithWordWork arcs table depth
    let cross := liftedArcsListWithChecks table arcs selected.1
    let joined := internal.1 ++ cross.1
    let unique := insertListWithChecks joined []
    (unique.1, prepared.2 + (4*projected.2+16*(d::ds).length+2) + selected.2 + internal.2 +
      (4*cross.2+18*(arcs.length+selected.1.length)+5) + (2*unique.2+16*joined.length+12) + (3*depth+6))

theorem liftCoreListWithWordWork_spec
    (run : List (V × V) → ℕ → List (V × V) → List (V × V) × ℕ)
    (plain : Arcs V → List (V × V) → Arcs V) (budget : ℕ → ℕ → ℕ → ℕ)
    (same : ∀ K T : List (V × V), K.Nodup →
      (run K (Fintype.card V) T).1.Nodup ∧ (run K (Fintype.card V) T).1.toFinset = plain K.toFinset T ∧
      (run K (Fintype.card V) T).2 ≤ budget (Fintype.card V) K.length T.length)
    (sub : ∀ K T, plain K T ⊆ K) (mono : ∀ n p, Monotone fun m => budget n m p)
    (arcs : List (V × V)) (vertices : List V) (demands : List (V × V)) (simple : vertices.Nodup)
    (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := arcs.length
    let out := liftCoreListWithWordWork run arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = liftedRun plain arcs.toFinset demands ∧
      out.2 ≤ 1+liftCoreWordBudget n m demands.length+budget n m demands.length := by
  cases demands with
  | nil => simp [liftCoreListWithWordWork, liftedRun]; omega
  | cons d rest =>
    let demands := d::rest
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let prepared := prepareCondensationWithWordWork arcs vertices
    let table := prepared.1.1
    let projected := projectPairsWithChecks table demands
    let selected := run prepared.1.2 vertices.length projected.1
    let internal := connectorsListWithWordWork arcs table vertices.length
    let cross := liftedArcsListWithChecks table arcs selected.1
    let joined := internal.1 ++ cross.1
    let unique := insertListWithChecks joined []
    have cover : vertices.toFinset = univ := by ext v; simp [enumerate v]
    have count : vertices.length = n := by
      rw [← List.toFinset_card_of_nodup simple, cover, card_univ]
    obtain ⟨labels, graphSimple, graph, graphSize, prepCost⟩ := prepareCondensationWithWordWork_spec arcs vertices simple enumerate
    have tableEq : table = vertices.map (fun v => (v,componentLabel arcs.toFinset v)) := labels
    obtain ⟨projection, cost⟩ := projectPairsWithChecks_spec (componentLabel arcs.toFinset) vertices demands enumerate
    have trace : projected.1 = demands.map (projectDemand arcs.toFinset) := by
      unfold projected
      rw [tableEq]
      exact projection
    have projectedCost : projected.2 ≤ p*(2*n) := by
      unfold projected
      rw [tableEq]
      simpa only [count] using cost
    have projectedLength : projected.1.length = p := by rw [trace, List.length_map]
    obtain ⟨selectedSimple, selectedSet, selectCost⟩ := same prepared.1.2 projected.1 graphSimple
    have graphEq : prepared.1.2.toFinset = condensation arcs.toFinset := graph
    have selectedEq : selected.1.toFinset = plain (condensation arcs.toFinset) (demands.map (projectDemand arcs.toFinset)) := by
      unfold selected
      rw [count, selectedSet, graphEq, trace]
    have selectedCap : selected.1.length ≤ m := by
      have simpleOut : selected.1.Nodup := by unfold selected; rw [count]; exact selectedSimple
      rw [← List.toFinset_card_of_nodup simpleOut, selectedEq]
      have arcCap : (condensation arcs.toFinset).card ≤ arcs.toFinset.card :=
        card_image_le.trans (card_le_card (filter_subset _ _))
      exact (card_le_card (sub _ _)).trans (arcCap.trans (List.toFinset_card_le _))
    have selectCap : selected.2 ≤ budget n m p := by
      unfold selected
      rw [count, ← projectedLength]
      exact selectCost.trans (mono _ _ graphSize)
    have tableCount : table.length = n := by rw [tableEq, List.length_map, count]
    obtain ⟨intSet, intCost⟩ := connectorsListWithWordWork_spec arcs vertices enumerate count
    obtain ⟨liftSet, liftCost⟩ := liftedArcsListWithChecks_spec vertices arcs selected.1 enumerate
    have intExact : internal.1.toFinset = connectors arcs.toFinset := by
      unfold internal
      rw [tableEq, count]
      exact intSet
    have intCap : internal.2 ≤ connectorsWordBudget n m := by
      unfold internal
      rw [tableEq, count]
      exact intCost
    have crossExact : cross.1.toFinset = liftedArcs arcs.toFinset selected.1.toFinset := by
      unfold cross
      rw [tableEq]
      exact liftSet
    have crossCap : cross.2 ≤ m*(2*n)+m*(2*m) := by
      unfold cross
      rw [tableEq]
      exact liftCost.trans (by rw [count]; gcongr)
    have joinedSize : joined.length ≤ 2*n+m := by
      have intSize := connectorsListWithWordWork_length arcs table vertices.length
      have crossSize := liftedArcsListWithChecks_length table arcs selected.1
      change internal.1.length ≤ 2*table.length at intSize
      change cross.1.length ≤ selected.1.length at crossSize
      rw [tableCount] at intSize
      rw [show joined.length = internal.1.length+cross.1.length from List.length_append]
      exact Nat.add_le_add intSize (crossSize.trans selectedCap)
    obtain ⟨uniqueSimple, uniqueSet, uniqueCost⟩ := insertListWithChecks_spec joined [] (by simp)
    have uniqueCap : unique.2 ≤ (2*n+m)*n^2 := by
      simpa only [Fintype.card_prod, ← pow_two] using uniqueCost.trans (Nat.mul_le_mul_right _ joinedSize)
    refine ⟨uniqueSimple, ?_, ?_⟩
    · change unique.1.toFinset = connectors arcs.toFinset ∪
        liftedArcs arcs.toFinset (plain (condensation arcs.toFinset) (demands.map (projectDemand arcs.toFinset)))
      change unique.1.toFinset = ([] : List (V × V)).toFinset ∪ joined.toFinset at uniqueSet
      rw [uniqueSet, List.toFinset_nil, empty_union, show joined.toFinset = _ from List.toFinset_append,
        intExact, crossExact, selectedEq]
    · change prepared.2 + (4*projected.2+16*p+2) + selected.2 + internal.2 +
        (4*cross.2+18*(m+selected.1.length)+5) + (2*unique.2+16*joined.length+12) + (3*vertices.length+6) ≤ _
      rw [count]
      have prepCap : prepared.2 ≤ prepareCondensationWordBudget n m := prepCost
      calc
        _ ≤ prepareCondensationWordBudget n m + (4*(p*(2*n))+16*p+2) + budget n m p +
            connectorsWordBudget n m + (4*(m*(2*n)+m*(2*m))+18*(m+m)+5) +
            (2*((2*n+m)*n^2)+16*(2*n+m)+12) + (3*n+6) := by gcongr
        _ = liftCoreWordBudget n m p + budget n m p := by unfold liftCoreWordBudget; ring
        _ ≤ 1+liftCoreWordBudget n m p+budget n m p := by omega

omit [Fintype V] in
/-- Exact general-digraph forward preserver with the explicit source-level
work charges of the supplied-list model. -/
def sinkPreserverListWithWordWork (arcs : List (V × V)) (vertices : List V) (demands : List (V × V)) :
    List (V × V) × ℕ :=
  liftCoreListWithWordWork (fun G depth D => forwardRunListWithWordWork G depth D []) arcs vertices demands

theorem sinkPreserverListWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let out := sinkPreserverListWithWordWork arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = sinkPreserver arcs.toFinset demands ∧
      out.2 ≤ 1+liftCoreWordBudget n m p+(1+p*(4+forwardStepWordBudget n m)) :=
  liftCoreListWithWordWork_spec _ forwardRun (fun n m p => 1+p*(4+forwardStepWordBudget n m))
    (fun K T _ => forwardRunListWithWordWork_spec K T [] (by simp))
    (fun _ _ => forwardRunFrom_subset (empty_subset _) _)
    (fun n p m k small => by dsimp only [forwardStepWordBudget,reachInListWordBudget]; gcongr)
    arcs vertices demands simple enumerate

omit [Fintype V] in
/-- The source-oriented evaluator also charges reversal of the input and
output pairs. -/
def sourcePreserverListWithWordWork (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) : List (V × V) × ℕ :=
  let result := sinkPreserverListWithWordWork (arcs.map Prod.swap) vertices (demands.map Prod.swap)
  (result.1.map Prod.swap, result.2 + 6*(arcs.length+demands.length+result.1.length)+8)

theorem sourcePreserverListWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let out := sourcePreserverListWithWordWork arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = sourcePreserver arcs.toFinset demands ∧
      out.2 ≤ 1+liftCoreWordBudget n m p+(1+p*(4+forwardStepWordBudget n m)) + 6*(m+p+n^2)+8 := by
  let result := sinkPreserverListWithWordWork (arcs.map Prod.swap) vertices (demands.map Prod.swap)
  obtain ⟨distinct, same, work⟩ := sinkPreserverListWithWordWork_spec
    (arcs.map Prod.swap) vertices (demands.map Prod.swap) simple enumerate
  have count : result.1.length ≤ (Fintype.card V)^2 := by
    rw [← List.toFinset_card_of_nodup (show result.1.Nodup from distinct), pow_two, ← Fintype.card_prod]
    exact card_le_univ _
  refine ⟨distinct.map Prod.swap_injective, ?_, ?_⟩
  · unfold sourcePreserverListWithWordWork sourcePreserver
    simp only [reverseArcList_toFinset, same]
  · change result.2 + 6*(arcs.length+demands.length+result.1.length)+8 ≤ _
    have bound : result.2 ≤ 1+liftCoreWordBudget (Fintype.card V) arcs.length demands.length +
        (1+demands.length*(4+forwardStepWordBudget (Fintype.card V) arcs.length)) := by
      simpa only [List.length_map] using work
    gcongr

private def prefixListsWithWordWork {A : Type*} : List A → List (List A) × ℕ
  | [] => ([[]],2)
  | a::rest =>
    let tail := prefixListsWithWordWork rest
    ([]::tail.1.map (a::·), tail.2+6+5*tail.1.length)

private theorem prefixListsWithWordWork_spec {A : Type*} (items : List A) :
    let out := prefixListsWithWordWork items
    out.1 = items.inits ∧ out.2 ≤ 10*(items.length+1)^2 := by
  induction items with
  | nil => simp [prefixListsWithWordWork]
  | cons a rest ih =>
    obtain ⟨same, bound⟩ := ih
    have length : (prefixListsWithWordWork rest).1.length = rest.length+1 := by rw [same,List.length_inits]
    refine ⟨?_,?_⟩
    · simp only [prefixListsWithWordWork, same, List.inits_cons]
    · change (prefixListsWithWordWork rest).2+6+5*(prefixListsWithWordWork rest).1.length ≤ _
      rw [length,List.length_cons]
      nlinarith

/-- Charge both the supplied evaluation and the list work to materialize
its answers on all revealed prefixes. Counter maintenance is excluded. -/
def prefixRunWithWordWork {A X : Type*} (evaluate : List A → X × ℕ) (items : List A) : List X × ℕ :=
  let prefixes := prefixListsWithWordWork items
  let out := mapListWithChecks evaluate prefixes.1
  (out.1, prefixes.2+out.2+6*prefixes.1.length+6)

theorem prefixRunWithWordWork_spec {A X Y : Type*} (evaluate : List A → X × ℕ)
    (forget : X → Y) (plain : List A → Y) (budget : ℕ → ℕ) (items : List A)
    (same : ∀ P, forget (evaluate P).1 = plain P)
    (cost : ∀ P, P <+: items → (evaluate P).2 ≤ budget items.length) :
    let out := prefixRunWithWordWork evaluate items
    out.1.map forget = items.inits.map plain ∧
      out.2 ≤ 10*(items.length+1)^2 + (items.length+1)*(budget items.length+6) + 6 := by
  let prefixes := prefixListsWithWordWork items
  obtain ⟨list, base⟩ := prefixListsWithWordWork_spec items
  change prefixes.1 = _ at list
  obtain ⟨actual, charged⟩ := mapListWithChecks_spec evaluate (fun P => (evaluate P).1)
    prefixes.1 (budget items.length) (fun _ _ => rfl) (fun P mem => cost P ((List.mem_inits _ _).mp (list ▸ mem)))
  constructor
  · change (mapListWithChecks evaluate prefixes.1).1.map forget = _
    rw [actual, list, List.map_map]
    simp only [Function.comp_def, same]
  · change prefixes.2+(mapListWithChecks evaluate prefixes.1).2+6*prefixes.1.length+6 ≤ _
    have length : prefixes.1.length = items.length+1 := by rw [list,List.length_inits]
    rw [length] at charged ⊢
    have bound := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add base charged) (6*(items.length+1))) 6
    exact bound.trans_eq (by ring)

/-- A polynomial tally for one revealed prefix in the forward orientation. -/
def sinkWordBudget (n m p : ℕ) : ℕ :=
  1+liftCoreWordBudget n m p+(1+p*(4+forwardStepWordBudget n m))

private theorem sinkWordBudget_mono_requests (n m : ℕ) : Monotone (sinkWordBudget n m) := by
  intro p q less
  unfold sinkWordBudget liftCoreWordBudget
  gcongr

theorem sinkPreserverListWithWordWork_prefixes (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let out := prefixRunWithWordWork (sinkPreserverListWithWordWork arcs vertices) demands
    out.1.map List.toFinset = demands.inits.map (sinkPreserver arcs.toFinset) ∧
      out.2 ≤ 10*(p+1)^2+(p+1)*(sinkWordBudget n m p+6)+6 :=
  prefixRunWithWordWork_spec _ List.toFinset (sinkPreserver arcs.toFinset)
    (sinkWordBudget (Fintype.card V) arcs.length) demands
    (fun P => (sinkPreserverListWithWordWork_spec arcs vertices P simple enumerate).2.1)
    (fun P earlier => (sinkPreserverListWithWordWork_spec arcs vertices P simple enumerate).2.2.trans
      (sinkWordBudget_mono_requests _ _ earlier.length_le))

/-- The forward tally plus the cost of reversing input and output pairs. -/
def sourceWordBudget (n m p : ℕ) : ℕ := sinkWordBudget n m p + 6*(m+p+n^2)+8

private theorem sourceWordBudget_mono_requests (n m : ℕ) : Monotone (sourceWordBudget n m) := by
  intro p q less
  unfold sourceWordBudget
  have base := sinkWordBudget_mono_requests n m less
  gcongr

theorem sourcePreserverListWithWordWork_prefixes (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let out := prefixRunWithWordWork (sourcePreserverListWithWordWork arcs vertices) demands
    out.1.map List.toFinset = demands.inits.map (sourcePreserver arcs.toFinset) ∧
      out.2 ≤ 10*(p+1)^2+(p+1)*(sourceWordBudget n m p+6)+6 :=
  prefixRunWithWordWork_spec _ List.toFinset (sourcePreserver arcs.toFinset)
    (sourceWordBudget (Fintype.card V) arcs.length) demands
    (fun P => (sourcePreserverListWithWordWork_spec arcs vertices P simple enumerate).2.1)
    (fun P earlier => (sourcePreserverListWithWordWork_spec arcs vertices P simple enumerate).2.2.trans
      (sourceWordBudget_mono_requests _ _ earlier.length_le))


omit [Fintype V] in
/-- Exact offline edge sets with structural charges for the list lift and
full greedy deletion. The model uses the supplied graph and vertex lists. -/
def offlinePreserverListWithWordWork (arcs : List (V × V)) (vertices : List V) (demands : List (V × V)) :
    List (V × V) × ℕ :=
  liftCoreListWithWordWork offlinePruneListWithWordWork arcs vertices demands

theorem offlinePreserverListWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let out := offlinePreserverListWithWordWork arcs vertices demands
    out.1.Nodup ∧ out.1.toFinset = offlinePreserver arcs.toFinset demands ∧
      out.2 ≤ 1+liftCoreWordBudget n m p+offlinePruningWordBudget n m p :=
  liftCoreListWithWordWork_spec _ offlinePrune offlinePruningWordBudget
    offlinePruneListWithWordWork_spec (fun K T => (offlinePrune_spec K T).1)
    offlinePruningWordBudget_mono_arcs
    arcs vertices demands simple enumerate

end OnlineReachabilityPreservers
