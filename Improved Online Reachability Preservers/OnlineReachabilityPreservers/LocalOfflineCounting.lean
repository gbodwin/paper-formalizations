import OnlineReachabilityPreservers.LocalBranching

/-! The sampled support and the off-base upper count in Appendix B. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

omit [LinearOrder I] [Fintype I] in
/-- A forward window contains at most `h+1` actual vertices. -/
def listWindowVertices (path : List V) (start : V) (h : ℕ) : Finset V :=
  path.toFinset.filter fun x => path.idxOf start ≤ path.idxOf x ∧ path.idxOf x ≤ path.idxOf start + h

omit [LinearOrder I] [Fintype I] in
theorem listWindowVertices_card (path : List V) (start : V) (h : ℕ) :
    (listWindowVertices path start h).card ≤ h + 1 := by
  calc
    _ ≤ (range (h + 1)).card := by
      apply card_le_card_of_injOn (fun x => path.idxOf x - path.idxOf start)
      · intro x hx
        have hi := (mem_filter.mp hx).2.2
        apply mem_range.mpr
        change path.idxOf x - path.idxOf start < h + 1
        omega
      · intro x hx y hy equal
        have left := (mem_filter.mp hx).2.1
        have right := (mem_filter.mp hy).2.1
        change path.idxOf x - path.idxOf start = path.idxOf y - path.idxOf start at equal
        exact (List.idxOf_inj (List.mem_toFinset.mp (mem_filter.mp hx).1)).mp (by omega)
    _ = _ := card_range _

omit [LinearOrder I] in
/-- All vertices in the branching windows of the selected base path. -/
def listBranchSupport (paths : I → List V) (b : I) (h : ℕ) : Finset V :=
  (paths b).toFinset.biUnion fun u => (occurrences (fun i => (paths i).toFinset) u).biUnion fun i =>
    listWindowVertices (paths i) u h

omit [LinearOrder I] in
theorem mem_listBranchSupport {paths : I → List V} {b : I} {h : ℕ} {x : V} :
    x ∈ listBranchSupport paths b h ↔ ∃ i u, InListBranchWindow paths b i h u x := by
  constructor
  · intro hx
    obtain ⟨u, hu, present⟩ := mem_biUnion.mp hx
    obtain ⟨i, hi, window⟩ := mem_biUnion.mp present
    obtain ⟨xi, after, close⟩ := mem_filter.mp window
    have path := (mem_occurrences (marks := fun j => (paths j).toFinset)).mp hi
    exact ⟨i, u, List.mem_toFinset.mp hu, List.mem_toFinset.mp path, List.mem_toFinset.mp xi, after, close⟩
  · rintro ⟨i, u, ub, ui, xi, after, close⟩
    exact mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr ub, mem_biUnion.mpr
      ⟨i, mem_occurrences.mpr (List.mem_toFinset.mpr ui),
        mem_filter.mpr ⟨List.mem_toFinset.mpr xi, after, close⟩⟩⟩

omit [LinearOrder I] in
theorem listBranchSupport_card (paths : I → List V) (b : I) (h : ℕ) :
    (listBranchSupport paths b h).card ≤
      ∑ u ∈ (paths b).toFinset, (occurrences (fun i => (paths i).toFinset) u).card * (h + 1) := by
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro u _
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ i ∈ occurrences (fun i => (paths i).toFinset) u, (h + 1) :=
      sum_le_sum fun i _ => listWindowVertices_card (paths i) u h
    _ = _ := by simp

omit [LinearOrder I] [Fintype I] in
/-- The branching path and its start are unique at an off-base vertex in a
full-bridge-free family with unique intersections. -/
theorem listBranchWindow_unique {paths : I → List V} (free : BridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {b a c : I} {x y u : V} {h : ℕ} (outside : u ∉ paths b)
    (one : InListBranchWindow paths b a h x u) (two : InListBranchWindow paths b c h y u) : a = c ∧ x = y := by
  obtain ⟨xb, xa, ua, xle, _⟩ := one
  obtain ⟨yb, yc, uc, yle, _⟩ := two
  have ba : b ≠ a := fun equal => outside (equal.symm ▸ ua)
  have bc : b ≠ c := fun equal => outside (equal.symm ▸ uc)
  by_cases equal : a = c
  · subst c
    exact ⟨rfl, unique ba xb xa yb yc⟩
  have ax : ListBefore paths a x u := ⟨xa, ua, xle.lt_of_ne fun eq =>
    outside (((List.idxOf_inj xa).mp eq) ▸ xb)⟩
  have cy : ListBefore paths c y u := ⟨yc, uc, yle.lt_of_ne fun eq =>
    outside (((List.idxOf_inj yc).mp eq) ▸ yb)⟩
  have distinct : x ≠ y := by
    rintro rfl
    exact listBefore_ne ax (unique equal xa yc ua uc)
  rcases listBefore_total xb yb distinct with earlier | later
  · exact ((free (show 3 ≤ 4 by decide)).false (threeListBridge bc ba.symm equal earlier cy ax)).elim
  · exact ((free (show 3 ≤ 4 by decide)).false (threeListBridge ba bc.symm (fun eq => equal eq.symm) later ax cy)).elim

variable [Fintype V]

/-- The local-order form of the combinatorial upper count in Lemma 41. -/
theorem lemma41_list_branch_count {paths : I → List V} (free : BridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (b : I) (h : ℕ) : (listOffBaseBranchTuples paths b h).card ≤
      ∑ i : I, ((paths i).toFinset ∩ listBranchSupport paths b h).card^2 := by
  classical
  let Q := listOffBaseBranchTuples paths b h
  let marked (i : I) := (paths i).toFinset ∩ listBranchSupport paths b h
  let candidates := (univ : Finset I).sigma fun i => marked i ×ˢ marked i
  have membership (w : Q) : QualifyingListBranchTuple paths b h w.val ∧ w.val.y ∉ paths b := by
    obtain ⟨one, two⟩ := mem_filter.mp w.property
    exact ⟨mem_listBranchTuples.mp one, two⟩
  let middle (w : Q) := Classical.choose (membership w).1.2.2.2.2
  have middleStep (w : Q) : ListIntersectionChain paths w.val.left (middle w) w.val.right w.val.x w.val.y :=
    Classical.choose_spec (membership w).1.2.2.2.2
  let charge (w : Q) : Σ _ : I, V × V := ⟨middle w, (w.val.x, w.val.y)⟩
  have count : Q.attach.card ≤ candidates.card := by
    apply card_le_card_of_injOn charge
    · intro w _
      have data := (membership w).1
      have first := mem_listBranchSupport.mpr ⟨w.val.left, w.val.leftStart, data.1⟩
      have last := mem_listBranchSupport.mpr ⟨w.val.right, w.val.rightStart, data.2.1⟩
      have through := (middleStep w).middle_step
      exact mem_sigma.mpr ⟨mem_univ _, mem_product.mpr
        ⟨mem_inter.mpr ⟨List.mem_toFinset.mpr through.1, first⟩,
          mem_inter.mpr ⟨List.mem_toFinset.mpr through.2.1, last⟩⟩⟩
    · rintro ⟨a, ha⟩ _ ⟨c, hc⟩ _ eq
      apply Subtype.ext
      have x : a.x = c.x := congrArg (fun z : Σ _ : I, V × V => z.2.1) eq
      have y : a.y = c.y := congrArg (fun z : Σ _ : I, V × V => z.2.2) eq
      have leftData := membership ⟨a, ha⟩
      have rightData := membership ⟨c, hc⟩
      have left := listBranchWindow_unique free unique leftData.1.2.2.1 leftData.1.1
        (x.symm ▸ rightData.1.1)
      have right := listBranchWindow_unique free unique leftData.2 leftData.1.2.1
        (y.symm ▸ rightData.1.2.1)
      cases a
      cases c
      simp only [BranchTuple.mk.injEq]
      exact ⟨left.1, right.1, left.2, right.2, x, y⟩
  simpa [Q, candidates, marked, card_sigma, card_product, pow_two] using count

end OnlineReachabilityPreservers
