import OnlineReachabilityPreservers.SccLiftListWork

/-! Include enumeration on already indexed finite vertices in the list-work bounds. -/

namespace OnlineReachabilityPreservers

private def finVertexSuffixWithWordWork (n : ℕ) : (k : ℕ) → k ≤ n → List (Fin n) × ℕ
  | 0, _ => ([],1)
  | k+1, fits =>
    let rest := finVertexSuffixWithWordWork n k (Nat.le_of_succ_le fits)
    (⟨n-(k+1), by omega⟩ :: rest.1, 8+rest.2)

private theorem finVertexSuffixWithWordWork_spec (n k : ℕ) (fits : k ≤ n) :
    let out := finVertexSuffixWithWordWork n k fits
    out.1.Nodup ∧ (∀ v : Fin n, v ∈ out.1 ↔ n-k ≤ v.val) ∧ out.2 = 8*k+1 := by
  induction k with
  | zero =>
    refine ⟨by simp [finVertexSuffixWithWordWork], fun v => ?_, rfl⟩
    have below := v.isLt
    simp only [finVertexSuffixWithWordWork, List.not_mem_nil, Nat.sub_zero, false_iff]
    omega
  | succ k ih =>
    let first : Fin n := ⟨n-(k+1), by omega⟩
    let rest := finVertexSuffixWithWordWork n k (Nat.le_of_succ_le fits)
    obtain ⟨nodup, members, tally⟩ := ih (Nat.le_of_succ_le fits)
    change (first :: rest.1).Nodup ∧ (∀ v : Fin n, v ∈ first :: rest.1 ↔ n-(k+1) ≤ v.val) ∧
      8+rest.2 = 8*(k+1)+1
    refine ⟨List.nodup_cons.mpr ⟨?_,nodup⟩, ?_, ?_⟩
    · intro inTail
      have across := (members first).mp inTail
      change n-k ≤ n-(k+1) at across
      omega
    · intro v
      rw [List.mem_cons, members]
      simp only [Fin.ext_iff, first]
      omega
    · change rest.2 = 8*k+1 at tally
      rw [tally]
      omega

/-- Enumerate the vertices when the graph keys are Fin n. The tally
charges each index subtraction, recursive step, and cell construction. -/
def finVerticesWithWordWork (n : ℕ) : List (Fin n) × ℕ :=
  finVertexSuffixWithWordWork n n le_rfl

theorem finVerticesWithWordWork_spec (n : ℕ) :
    let out := finVerticesWithWordWork n
    out.1.Nodup ∧ (∀ v : Fin n, v ∈ out.1) ∧ out.2 = 8*n+1 := by
  obtain ⟨simple, all, cost⟩ := finVertexSuffixWithWordWork_spec n n le_rfl
  exact ⟨simple, fun v => (all v).mpr (by simp), cost⟩

private theorem finVertexSuffixWithWordWork_pairwise (n k : ℕ) (fits : k ≤ n) :
    (finVertexSuffixWithWordWork n k fits).1.Pairwise (· ≤ ·) := by
  induction k with
  | zero => exact List.Pairwise.nil
  | succ k ih =>
    change (⟨n-(k+1),by omega⟩ :: (finVertexSuffixWithWordWork n k (Nat.le_of_succ_le fits)).1).Pairwise (· ≤ ·)
    refine List.pairwise_cons.mpr ⟨fun v present => ?_, ih (Nat.le_of_succ_le fits)⟩
    have index := ((finVertexSuffixWithWordWork_spec n k (Nat.le_of_succ_le fits)).2.1 v).mp present
    change n-(k+1) ≤ v.val
    omega

/-- The metered enumeration has the canonical increasing vertex order. -/
theorem finVerticesWithWordWork_eq_sort (n : ℕ) :
    (finVerticesWithWordWork n).1 = (Finset.univ : Finset (Fin n)).sort := by
  let rows := (Finset.univ : Finset (Fin n))
  obtain ⟨unique, full, _⟩ := finVerticesWithWordWork_spec n
  apply List.Perm.eq_of_pairwise' (finVertexSuffixWithWordWork_pairwise n n le_rfl) (rows.pairwise_sort _)
  exact (List.perm_ext_iff_of_nodup unique (rows.sort_nodup _)).mpr fun v => by simp [rows, full v]

def withFinVerticesWithWordWork {n : ℕ} {A : Type*} (run : List (Fin n) → A × ℕ) : A × ℕ :=
  let vertices := finVerticesWithWordWork n
  let out := run vertices.1
  (out.1, vertices.2+out.2+4)

theorem withFinVerticesWithWordWork_spec {n : ℕ} {A : Type*} {P : A → Prop}
    (run : List (Fin n) → A × ℕ) (budget : ℕ)
    (correct : ∀ vertices, vertices.Nodup → (∀ v, v ∈ vertices) →
      P (run vertices).1 ∧ (run vertices).2 ≤ budget) :
    let out := withFinVerticesWithWordWork run
    P out.1 ∧ out.2 ≤ 8*n+1+budget+4 := by
  obtain ⟨simple, all, cost⟩ := finVerticesWithWordWork_spec n
  obtain ⟨same, work⟩ := correct _ simple all
  exact ⟨same, Nat.add_le_add_right (Nat.add_le_add cost.le work) 4⟩

/-- A source-level bound including the vertex enumeration for all forward
prefixes of a graph whose vertices are Fin n. -/
theorem sinkFinPreserverListWithWordWork_prefixes {n : ℕ}
    (arcs demands : List (Fin n × Fin n)) :
    let p := demands.length
    let out := withFinVerticesWithWordWork
      (fun vertices => prefixRunWithWordWork (sinkPreserverListWithWordWork arcs vertices) demands)
    out.1.map List.toFinset = demands.inits.map (sinkPreserver arcs.toFinset) ∧
      out.2 ≤ 8*n+1+(10*(p+1)^2+(p+1)*(sinkWordBudget n arcs.length p+6)+6)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun sets => sets.map List.toFinset = demands.inits.map (sinkPreserver arcs.toFinset))
    (fun vertices => prefixRunWithWordWork (sinkPreserverListWithWordWork arcs vertices) demands) _ ?_
  intro vertices simple all
  simpa only [Fintype.card_fin] using sinkPreserverListWithWordWork_prefixes arcs vertices demands simple all

/-- A source-level bound including the same enumeration for all reverse
prefixes. -/
theorem sourceFinPreserverListWithWordWork_prefixes {n : ℕ}
    (arcs demands : List (Fin n × Fin n)) :
    let p := demands.length
    let out := withFinVerticesWithWordWork
      (fun vertices => prefixRunWithWordWork (sourcePreserverListWithWordWork arcs vertices) demands)
    out.1.map List.toFinset = demands.inits.map (sourcePreserver arcs.toFinset) ∧
      out.2 ≤ 8*n+1+(10*(p+1)^2+(p+1)*(sourceWordBudget n arcs.length p+6)+6)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun sets => sets.map List.toFinset = demands.inits.map (sourcePreserver arcs.toFinset))
    (fun vertices => prefixRunWithWordWork (sourcePreserverListWithWordWork arcs vertices) demands) _ ?_
  intro vertices simple all
  simpa only [Fintype.card_fin] using sourcePreserverListWithWordWork_prefixes arcs vertices demands simple all

/-- A source-level bound including vertex enumeration for greedy offline
deletion and lifting. -/
theorem offlineFinPreserverListWithWordWork_spec {n : ℕ}
    (arcs demands : List (Fin n × Fin n)) :
    let m := arcs.length
    let p := demands.length
    let out := withFinVerticesWithWordWork
      (fun vertices => offlinePreserverListWithWordWork arcs vertices demands)
    out.1.Nodup ∧ out.1.toFinset = offlinePreserver arcs.toFinset demands ∧
      out.2 ≤ 8*n+1+(1+liftCoreWordBudget n m p+offlinePruningWordBudget n m p)+4 := by
  have checked := withFinVerticesWithWordWork_spec
    (P := fun edges => edges.Nodup ∧ edges.toFinset = offlinePreserver arcs.toFinset demands)
    (fun vertices => offlinePreserverListWithWordWork arcs vertices demands)
    (1+liftCoreWordBudget n arcs.length demands.length+offlinePruningWordBudget n arcs.length demands.length) (by
      intro vertices simple all
      obtain ⟨simpleOut, same, cost⟩ := offlinePreserverListWithWordWork_spec arcs vertices demands simple all
      exact ⟨⟨simpleOut, same⟩, by simpa only [Fintype.card_fin] using cost⟩)
  exact ⟨checked.1.1, checked.1.2, checked.2⟩

end OnlineReachabilityPreservers
