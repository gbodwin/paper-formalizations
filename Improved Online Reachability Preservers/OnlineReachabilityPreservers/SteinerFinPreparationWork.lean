import OnlineReachabilityPreservers.SteinerTemplatePreparationWork

/-! Prepare the exact Steiner hop table and paired forest with explicit lists. -/

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

private abbrev DistanceRows (V : Type*) := List ((V × V) × ℕ)

private def prependDistanceRowsFromSource {V : Type*} [LinearOrder V]
    (arcs : List (V × V)) (source : V) (n : ℕ) (tail : DistanceRows V) :
    List V → DistanceRows V × ℕ
  | [] => (tail, 3)
  | target :: targets =>
    let hop := hopsListWithWordWork arcs source target n
    let rest := prependDistanceRowsFromSource arcs source n tail targets
    (((source,target),hop.1) :: rest.1, hop.2+rest.2+16)

private theorem prependDistanceRowsFromSource_spec (arcs : List (V × V))
    (source : V) (tail : DistanceRows V) (targets : List V) :
    let n := Fintype.card V
    let out := prependDistanceRowsFromSource arcs source n tail targets
    out.1 = (targets.map fun target => ((source,target),hops arcs.toFinset source target)) ++ tail ∧
      out.2 ≤ targets.length*(hopsListWordBudget n arcs.length+16)+3 := by
  induction targets with
  | nil => simp [prependDistanceRowsFromSource]
  | cons target targets ih =>
    obtain ⟨rows, work⟩ := ih
    obtain ⟨hop, charge⟩ := hopsListWithWordWork_spec arcs source target
    simp only [prependDistanceRowsFromSource, rows, hop, List.map_cons, List.cons_append, List.length_cons]
    refine ⟨trivial, ?_⟩
    rw [Nat.succ_mul]
    omega

private def distanceRowsWithWordWork {V : Type*} [LinearOrder V] (arcs : List (V × V)) (n : ℕ)
    (targets : List V) : List V → DistanceRows V × ℕ
  | [] => ([], 3)
  | source :: sources =>
    let rest := distanceRowsWithWordWork arcs n targets sources
    let prepended := prependDistanceRowsFromSource arcs source n rest.1 targets
    (prepended.1, rest.2+prepended.2+8)

private theorem distanceRowsWithWordWork_spec (arcs : List (V × V)) (targets sources : List V) :
    let n := Fintype.card V
    let out := distanceRowsWithWordWork arcs n targets sources
    out.1 = (sources.flatMap fun source => targets.map fun target =>
      ((source,target),hops arcs.toFinset source target)) ∧
    out.2 ≤ sources.length*(targets.length*(hopsListWordBudget n arcs.length+16)+11)+3 := by
  induction sources with
  | nil => simp [distanceRowsWithWordWork]
  | cons source sources ih =>
    obtain ⟨rest, restWork⟩ := ih
    let n := Fintype.card V
    let out := distanceRowsWithWordWork arcs n targets sources
    obtain ⟨prepended, work⟩ := prependDistanceRowsFromSource_spec arcs source out.1 targets
    change out.1 = _ at rest
    change out.2 ≤ _ at restWork
    change (prependDistanceRowsFromSource arcs source n out.1 targets).1 = _ at prepended
    change (prependDistanceRowsFromSource arcs source n out.1 targets).2 ≤ _ at work
    change (prependDistanceRowsFromSource arcs source n out.1 targets).1 = _ ∧
      out.2+(prependDistanceRowsFromSource arcs source n out.1 targets).2+8 ≤ _
    constructor
    · rw [prepended, rest, List.flatMap_cons]
    · rw [List.length_cons, Nat.succ_mul]
      omega

/-- Build an all-pairs hop table over the supplied vertex order using the
list-backed reverse-search evaluator. The graph is supplied as its arc list. -/
def distanceTableFromListsWithWordWork {V : Type*} [LinearOrder V] (arcs : List (V × V)) (n : ℕ)
    (vertices : List V) : DistanceRows V × ℕ :=
  distanceRowsWithWordWork arcs n vertices vertices

def distanceTableListWorkPolynomial (n m : ℕ) : ℕ :=
  n*(n*(hopsListWordBudget n m+16)+11)+3

theorem distanceTableFromListsWithWordWork_spec (arcs : List (V × V)) :
    let n := Fintype.card V
    let vertices := (Finset.univ : Finset V).sort
    let out := distanceTableFromListsWithWordWork arcs n vertices
    out.1 = (vertices.flatMap fun s => vertices.map fun t => ((s,t),hops arcs.toFinset s t)) ∧
      out.2 ≤ distanceTableListWorkPolynomial n arcs.length := by
  have size : ((Finset.univ : Finset V).sort).length = Fintype.card V := by simp
  obtain ⟨rows, work⟩ := distanceRowsWithWordWork_spec arcs ((Finset.univ : Finset V).sort)
    ((Finset.univ : Finset V).sort)
  rw [size] at work
  exact ⟨rows, work⟩

/-- Indexed vertices are listed once for both the distance table and the
paired forest. The two tallies charge the setup of their respective lists. -/
def finSteinerTemplateInputsWithWordWork {n : ℕ} (arcs : List (Fin n × Fin n)) (height : ℕ) :=
  let vertices := finVerticesWithWordWork n
  let table := distanceTableFromListsWithWordWork arcs n vertices.1
  let forest := heightForestListWithDistanceWork n height (fun i => (i,1)) vertices.1 table.1
  ((table.1,table.2+vertices.2+8),forest)

local instance {n height : ℕ} : DecidableEq (HeightForestVertex (Fin n) height) :=
  (inferInstance : LinearOrder (HeightForestVertex (Fin n) height)).toDecidableEq

theorem finSteinerTemplateInputsWithWordWork_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    let out := finSteinerTemplateInputsWithWordWork arcs height
    out.1.1 = (distanceTableWithSearchWork G).1 ∧
      out.2.1.toFinset = heightForest G height ∧ out.2.1.Nodup ∧
      out.1.2 ≤ distanceTableListWorkPolynomial n arcs.length+8*n+9 ∧
      out.2.2 ≤ heightForestListDistanceWorkPolynomial n height 1 := by
  let vertices := finVerticesWithWordWork n
  let table := distanceTableFromListsWithWordWork arcs n vertices.1
  obtain ⟨distinct, all, enumeration⟩ := finVerticesWithWordWork_spec n
  have sorted : vertices.1 = (Finset.univ : Finset (Fin n)).sort := finVerticesWithWordWork_eq_sort n
  obtain ⟨rows,work⟩ := distanceTableFromListsWithWordWork_spec arcs
  simp only [Fintype.card_fin, ← sorted, same] at rows work
  have tableEq : table.1 = (distanceTableWithSearchWork G).1 :=
    rows.trans (by simpa only [← sorted] using (distanceTableWithSearchWork_rows G).symm)
  have forest :=
    heightForestListWithDistanceWork_spec G (n := n) (by simp) (Equiv.refl (Fin n)) (fun i => (i,1)) 1
      (fun _ => rfl) (fun _ => le_rfl) vertices.1 all distinct height
  let found := heightForestListWithDistanceWork n height (fun i => (i,1)) vertices.1 table.1
  have forestSpec : found.1.toFinset = heightForest G height ∧ found.1.Nodup ∧
      found.2 ≤ heightForestListDistanceWorkPolynomial n height 1 := by
    dsimp only [found]
    rw [tableEq]
    exact forest
  change table.1 = _ ∧ found.1.toFinset = _ ∧ found.1.Nodup ∧
    table.2+vertices.2+8 ≤ _ ∧ found.2 ≤ _
  change table.2 ≤ _ at work
  change vertices.2 = _ at enumeration
  exact ⟨tableEq,forestSpec.1,forestSpec.2.1,by omega,forestSpec.2.2⟩

private def arcsFromDistinctList {W : Type*} (rows : List (W × W)) (distinct : rows.Nodup) : Arcs W :=
  ⟨(rows : Multiset (W × W)),Multiset.coe_nodup.mpr distinct⟩

private theorem arcsFromDistinctList_eq {W : Type*} [DecidableEq W] (rows : List (W × W))
    (distinct : rows.Nodup) :
    arcsFromDistinctList rows distinct = rows.toFinset := by
  ext e
  simp [arcsFromDistinctList]

/-- Reuse the newly built hop table and forest in the ordinary weighted plan.
The forest list is already duplicate-free, so passing it to that plan
requires no deduplication. The final field retains the old weight-read tally. -/
def prepareFinSteinerForSeedWithWordWork {n : ℕ} (G : Arcs (Fin n)) (arcs : List (Fin n × Fin n))
    (same : arcs.toFinset = G) (height : ℕ) : SteinerSeedPreparation G height :=
  let out := finSteinerTemplateInputsWithWordWork arcs height
  let spec := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let links := arcsFromDistinctList out.2.1 spec.2.2.1
  let exactForest := (arcsFromDistinctList_eq out.2.1 spec.2.2.1).trans spec.2.1
  prepareEarlyDistanceTableForSeedFrom G height out.1 spec.1 (links,out.2.2+5) exactForest

/-- The shared list preparation preserves the weighted evaluator and its
scale. Its hop and forest work bounds cover their explicit list builders. -/
theorem prepareFinSteinerForSeedWithWordWork_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    let out := prepareFinSteinerForSeedWithWordWork G arcs same height
    let old := prepareEarlyDistanceTableForSeed G height
    out = (old.1,old.2.1,out.2.2.1,out.2.2.2.1,old.2.2.2.2) ∧
      out.2.2.1 ≤ distanceTableListWorkPolynomial n arcs.length+8*n+9 ∧
      out.2.2.2.1 ≤ heightForestListDistanceWorkPolynomial n height 1+5 := by
  let out := finSteinerTemplateInputsWithWordWork arcs height
  let spec := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let links := arcsFromDistinctList out.2.1 spec.2.2.1
  let exactForest := (arcsFromDistinctList_eq out.2.1 spec.2.2.1).trans spec.2.1
  exact ⟨prepareEarlyDistanceTableForSeedFrom_eq G height out.1 spec.1 (links,out.2.2+5) exactForest,
    spec.2.2.2.1, Nat.add_le_add_right spec.2.2.2.2 5⟩

end OnlineReachabilityPreservers
