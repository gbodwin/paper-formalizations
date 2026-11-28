import Mathlib.Combinatorics.SimpleGraph.Finite
import OnlineReachabilityPreservers.HalfFiveIncidenceHitting

/-! Keep overlapping rows while bounding the local opposite constraint degrees. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem erase_to_degree_two {A : Type*} [DecidableEq A]
    (ground : Finset A) (family : Finset (Finset A)) (within : ∀ edge ∈ family, edge ⊆ ground) :
    ∃ deleted ⊆ ground, 3*deleted.card ≤ family.card ∧
      ∀ x, (family.filter fun edge => x ∈ edge ∧ Disjoint edge deleted).card ≤ 2 := by
  classical
  induction size : family.card using Nat.strong_induction_on generalizing ground family with
  | h size ih =>
    by_cases heavy : ∃ x ∈ ground, 3 ≤ (family.filter fun edge => x ∈ edge).card
    · obtain ⟨x,xIn,large⟩ := heavy
      let through := family.filter fun edge => x ∈ edge
      let survivors := family \ through
      have subset := filter_subset (fun edge => x ∈ edge) family
      have split : survivors.card+through.card = family.card := card_sdiff_add_card_eq_card subset
      have avoids {edge : Finset A} (on : edge ∈ survivors) : x ∉ edge := fun fresh =>
        (mem_sdiff.mp on).2 (mem_filter.mpr ⟨(mem_sdiff.mp on).1,fresh⟩)
      have stays : ∀ edge ∈ survivors, edge ⊆ ground.erase x := by
        intro edge present y atEdge
        exact mem_erase.mpr ⟨fun equal => avoids present (equal ▸ atEdge),within edge (mem_sdiff.mp present).1 atEdge⟩
      have fewer : survivors.card < family.card := by change 3 ≤ through.card at large; omega
      obtain ⟨deleted,contained,cost,light⟩ := ih survivors.card (by omega) (ground.erase x) survivors stays rfl
      have fresh : x ∉ deleted := fun member => (mem_erase.mp (contained member)).1 rfl
      refine ⟨insert x deleted,insert_subset_iff.mpr ⟨xIn,contained.trans (erase_subset _ _)⟩,?_,?_⟩
      · rw [card_insert_of_notMem fresh]
        change 3 ≤ through.card at large
        omega
      · intro y
        have equal : (family.filter fun e => y ∈ e ∧ Disjoint e (insert x deleted)) =
            survivors.filter (fun e => y ∈ e ∧ Disjoint e deleted) := by
          ext e
          simp only [mem_filter,disjoint_insert_right,survivors,through,mem_sdiff]
          constructor
          · rintro ⟨on,atY,avoidsX,apart⟩
            exact ⟨⟨on,fun together => avoidsX together.2⟩,atY,apart⟩
          · rintro ⟨⟨on,avoidsX⟩,atY,apart⟩
            exact ⟨on,atY,fun atX => avoidsX ⟨on,atX⟩,apart⟩
        rw [equal]
        exact light y
    · refine ⟨∅,empty_subset _,by simp,?_⟩
      intro x
      simp only [disjoint_empty_right,and_true]
      by_cases member : x ∈ ground
      · exact Nat.lt_succ_iff.mp (Nat.lt_of_not_ge fun h => heavy ⟨x,member,h⟩)
      · have noEdge : (family.filter fun e => x ∈ e) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro edge on
          exact member (within edge (mem_filter.mp on).1 (mem_filter.mp on).2)
        simp [noEdge]

private theorem incidenceRectangle_survives {n p : ℕ} {paths : Fin p → List (Fin n)}
    {deleted : Finset (Fin p × Fin n)} {i j : Fin p} {x y : Fin n}
    (rows : i ≠ j) (cols : x ≠ y)
    (xi : x ∈ erasePieceIncidences paths deleted i) (yi : y ∈ erasePieceIncidences paths deleted i)
    (xj : x ∈ erasePieceIncidences paths deleted j) (yj : y ∈ erasePieceIncidences paths deleted j) :
    commonVertexPairRectangle i j x y ∈ commonVertexPairRectangles paths ∧
      Disjoint (commonVertexPairRectangle i j x y) deleted := by
  obtain ⟨xi,notXi⟩ := mem_erasePieceIncidences.mp xi
  obtain ⟨yi,notYi⟩ := mem_erasePieceIncidences.mp yi
  obtain ⟨xj,notXj⟩ := mem_erasePieceIncidences.mp xj
  obtain ⟨yj,notYj⟩ := mem_erasePieceIncidences.mp yj
  refine ⟨commonVertexPairRectangle_mem rows cols xi yi xj yj,disjoint_left.mpr ?_⟩
  rintro ⟨row,col⟩ present deletedCell
  obtain ⟨rowOn,colOn⟩ := mem_product.mp present
  simp only [mem_insert,mem_singleton] at rowOn colOn
  rcases rowOn with rfl | rfl <;> rcases colOn with rfl | rfl
  · exact notXi deletedCell
  · exact notYi deletedCell
  · exact notXj deletedCell
  · exact notYj deletedCell

/-- The row names at a fixed vertex carrying that incidence. -/
def commonVertexRows {n p : ℕ} (paths : Fin p → List (Fin n)) (v : Fin n) : Finset (Fin p) :=
  (univ : Finset (Fin p)).filter fun i => v ∈ paths i

theorem mem_commonVertexRows {n p : ℕ} {paths : Fin p → List (Fin n)} {v : Fin n} {i : Fin p} :
    i ∈ commonVertexRows paths v ↔ v ∈ paths i := by simp [commonVertexRows]

/-- At a fixed vertex, two incident rows are partners when they also
contain another common vertex. -/
def commonRowPartnerGraph {n p : ℕ} (paths : Fin p → List (Fin n)) (v : Fin n) :
    SimpleGraph (commonVertexRows paths v) where
  Adj a b := a ≠ b ∧ ∃ x, x ≠ v ∧ x ∈ paths a.val ∧ x ∈ paths b.val
  symm := ⟨by
    rintro a b ⟨distinct,x,elsewhere,left,right⟩
    exact ⟨distinct.symm,x,elsewhere,right,left⟩⟩
  loopless := ⟨fun _ same => same.1 rfl⟩

/-- On a fixed row, two vertices are partners when some other row
contains both. -/
def commonColumnPartnerGraph {n p : ℕ} (paths : Fin p → List (Fin n)) (i : Fin p) :
    SimpleGraph (paths i).toFinset where
  Adj a b := a ≠ b ∧ ∃ j, j ≠ i ∧ a.val ∈ paths j ∧ b.val ∈ paths j
  symm := ⟨by
    rintro a b ⟨distinct,j,elsewhere,left,right⟩
    exact ⟨distinct.symm,j,elsewhere,right,left⟩⟩
  loopless := ⟨fun _ same => same.1 rfl⟩

private noncomputable def remainingRectanglesAt {n p : ℕ} (paths : Fin p → List (Fin n))
    (deleted : Finset (Fin p × Fin n)) (cell : Fin p × Fin n) : Finset (Finset (Fin p × Fin n)) := by
  classical
  exact (commonVertexPairRectangles paths).filter fun edge => cell ∈ edge ∧ Disjoint edge deleted

open scoped Classical in
private theorem commonRow_degree_le_remainingRectangles {n p : ℕ} (paths : Fin p → List (Fin n))
    (deleted : Finset (Fin p × Fin n)) (v : Fin n)
    (i : commonVertexRows (erasePieceIncidences paths deleted) v) :
    (commonRowPartnerGraph (erasePieceIncidences paths deleted) v).degree i ≤
      (remainingRectanglesAt paths deleted (i.val,v)).card := by
  classical
  let kept := erasePieceIncidences paths deleted
  let graph := commonRowPartnerGraph kept v
  let near := graph.neighborFinset i
  let remain := remainingRectanglesAt paths deleted (i.val,v)
  have assigned (j : near) : ∃ u, u ≠ v ∧ commonVertexPairRectangle i.val j.val.val v u ∈ remain := by
    obtain ⟨different,u,elsewhere,iu,ju⟩ := (graph.mem_neighborFinset _ _).mp j.property
    have iv : v ∈ kept i.val := mem_commonVertexRows.mp i.property
    have jv : v ∈ kept j.val.val := mem_commonVertexRows.mp j.val.property
    have distinct : i.val ≠ j.val.val := fun equal => different (Subtype.ext equal)
    obtain ⟨rect,untouched⟩ := incidenceRectangle_survives distinct elsewhere.symm iv iu jv ju
    refine ⟨u,elsewhere,mem_filter.mpr ⟨rect,?_,untouched⟩⟩
    exact mem_product.mpr ⟨mem_insert_self _ _,mem_insert_self _ _⟩
  choose point outside present using assigned
  let place (j : near) : remain := ⟨commonVertexPairRectangle i.val j.val.val v (point j),present j⟩
  have injective : Function.Injective place := by
    intro a b equal
    have same : commonVertexPairRectangle i.val a.val.val v (point a) =
        commonVertexPairRectangle i.val b.val.val v (point b) := congrArg Subtype.val equal
    have here : (a.val.val,v) ∈ commonVertexPairRectangle i.val a.val.val v (point a) :=
      mem_product.mpr ⟨mem_insert_of_mem (mem_singleton_self _),mem_insert_self _ _⟩
    have there : (a.val.val,v) ∈ commonVertexPairRectangle i.val b.val.val v (point b) := same ▸ here
    have options : a.val.val = i.val ∨ a.val.val = b.val.val := by
      simpa only [mem_insert,mem_singleton] using (mem_product.mp there).1
    have aDistinct : i ≠ a.val := ((graph.mem_neighborFinset _ _).mp a.property).1
    exact Subtype.ext (Subtype.ext (options.resolve_left (fun wrong => aDistinct (Subtype.ext wrong.symm))))
  have count := Fintype.card_le_of_injective place injective
  simpa only [Fintype.card_coe,near,remain,SimpleGraph.card_neighborFinset_eq_degree,graph,kept] using count

open scoped Classical in
private theorem commonColumn_degree_le_remainingRectangles {n p : ℕ} (paths : Fin p → List (Fin n))
    (deleted : Finset (Fin p × Fin n)) (i : Fin p) (v : (erasePieceIncidences paths deleted i).toFinset) :
    (commonColumnPartnerGraph (erasePieceIncidences paths deleted) i).degree v ≤
      (remainingRectanglesAt paths deleted (i,v.val)).card := by
  classical
  let kept := erasePieceIncidences paths deleted
  let graph := commonColumnPartnerGraph kept i
  let near := graph.neighborFinset v
  let remain := remainingRectanglesAt paths deleted (i,v.val)
  have assigned (u : near) : ∃ j, j ≠ i ∧ commonVertexPairRectangle i j v.val u.val.val ∈ remain := by
    obtain ⟨different,j,elsewhere,jv,ju⟩ := (graph.mem_neighborFinset _ _).mp u.property
    have iv : v.val ∈ kept i := List.mem_toFinset.mp v.property
    have iu : u.val.val ∈ kept i := List.mem_toFinset.mp u.val.property
    have distinct : v.val ≠ u.val.val := fun equal => different (Subtype.ext equal)
    obtain ⟨rect,untouched⟩ := incidenceRectangle_survives elsewhere.symm distinct iv iu jv ju
    refine ⟨j,elsewhere,mem_filter.mpr ⟨rect,?_,untouched⟩⟩
    exact mem_product.mpr ⟨mem_insert_self _ _,mem_insert_self _ _⟩
  choose row outside present using assigned
  let place (u : near) : remain := ⟨commonVertexPairRectangle i (row u) v.val u.val.val,present u⟩
  have injective : Function.Injective place := by
    intro a b equal
    have same : commonVertexPairRectangle i (row a) v.val a.val.val =
        commonVertexPairRectangle i (row b) v.val b.val.val := congrArg Subtype.val equal
    have here : (i,a.val.val) ∈ commonVertexPairRectangle i (row a) v.val a.val.val :=
      mem_product.mpr ⟨mem_insert_self _ _,mem_insert_of_mem (mem_singleton_self _)⟩
    have there : (i,a.val.val) ∈ commonVertexPairRectangle i (row b) v.val b.val.val := same ▸ here
    have options : a.val.val = v.val ∨ a.val.val = b.val.val := by
      simpa only [mem_insert,mem_singleton] using (mem_product.mp there).2
    have aDistinct : v ≠ a.val := ((graph.mem_neighborFinset _ _).mp a.property).1
    exact Subtype.ext (Subtype.ext (options.resolve_left (fun wrong => aDistinct (Subtype.ext wrong.symm))))
  have count := Fintype.card_le_of_injective place injective
  simpa only [Fintype.card_coe,near,remain,SimpleGraph.card_neighborFinset_eq_degree,graph,kept] using count

open scoped Classical in
/-- Delete at most one incidence per three original common-vertex-pair
constraints. In the remainder the row-partner graph at every vertex and
the vertex-partner graph on every row both have maximum degree two. -/
theorem common_vertex_pairs_local_degree_two {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) :
    let M := ∑ i, (paths i).length
    let E := commonVertexPairCount paths
    ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (paths i)) ∧
      3*M ≤ 3*(∑ i, (kept i).length)+E ∧
      (∀ v (i : commonVertexRows kept v), (commonRowPartnerGraph kept v).degree i ≤ 2) ∧
      (∀ i (v : (kept i).toFinset), (commonColumnPartnerGraph kept i).degree v ≤ 2) := by
  classical
  dsimp only
  let ground := pieceIncidences paths univ
  let family := commonVertexPairRectangles paths
  obtain ⟨deleted,contained,cost,small⟩ := erase_to_degree_two ground family (commonVertexPairRectangles_support paths)
  let kept := erasePieceIncidences paths deleted
  have mass := erasePieceIncidences_mass_add_loss simple univ deleted
  rw [inter_eq_right.mpr contained] at mass
  change (∑ i, (kept i).length) + deleted.card = ∑ i, (paths i).length at mass
  have count := cost.trans (commonVertexPairRectangles_card_le paths)
  refine ⟨kept,erasePieceIncidences_sublist paths deleted,by omega,?_,?_⟩
  · intro v i
    exact (commonRow_degree_le_remainingRectangles paths deleted v i).trans (small (i.val,v))
  · intro i v
    exact (commonColumn_degree_le_remainingRectangles paths deleted i v).trans (small (i,v.val))

end OnlineReachabilityPreservers
