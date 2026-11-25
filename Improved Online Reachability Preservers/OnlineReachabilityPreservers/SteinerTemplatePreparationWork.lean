import OnlineReachabilityPreservers.DeterministicEnumerationWork
import OnlineReachabilityPreservers.SteinerPairedTemplateListWork

/-! Build the exact paired templates from one original-graph distance table. -/

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

private def templateReadWithWordWork (n : ℕ) (read : V × V → ℕ × ℕ) (a b : V) : Bool × ℕ :=
  let entry := read (b,a)
  (decide (entry.1 ≤ n),8*entry.2+8)

private def templateDistanceReadWork (n : ℕ) : ℕ := 8*n^2+8

/-- Build the two directed copies from the same distance table by swapping
the query endpoints. The tally includes a fixed allowance for each visited
row, treating original-vertex key comparisons as unit operations. -/
def heightForestListWithDistanceWork (n height : ℕ) (label : Fin n → V × ℕ) (roots : List V)
    (rows : List ((V × V) × ℕ)) :=
  let read := readDistanceRow rows
  pairedTemplateEnumeratedWithWordWork n height label (templateReadWithWordWork n read)
    (templateReadWithWordWork n (fun d => read d.swap)) roots

/-- At fixed height this is polynomial in the graph size and the supplied
per-label work bound. -/
def heightForestListDistanceWorkPolynomial (n height labelWork : ℕ) : ℕ :=
  let H := (n+1)^height
  (heightNodeIndexWordBudget height labelWork+9)*H+
    n*(2*H*((templateDistanceReadWork n+16)*height+34)+32)+5*height+16

theorem heightForestListWithDistanceWork_spec (G : Arcs V) {n : ℕ} (size : n = Fintype.card V)
    (vertices : V ≃ Fin n) (label : Fin n → V × ℕ) (labelWork : ℕ)
    (same : ∀ i, (label i).1 = vertices.symm i) (cost : ∀ i, (label i).2 ≤ labelWork)
    (roots : List V) (allRoots : ∀ v, v ∈ roots) (rootSimple : roots.Nodup) (height : ℕ) :
    let out := heightForestListWithDistanceWork n height label roots (distanceTableWithSearchWork G).1
    out.1.toFinset = heightForest G height ∧ out.1.Nodup ∧
      out.2 ≤ heightForestListDistanceWorkPolynomial n height labelWork := by
  let read := readDistanceRow (distanceTableWithSearchWork G).1
  have correct (d : V × V) : (read d).1 ≤ n ↔ Reach G d.1 d.2 := by
    rw [size, (distanceTableReadWithSearchWork_spec G d).1, hops_le_vertices_iff]
  have readWork (d : V × V) : 8*(read d).2+8 ≤ templateDistanceReadWork n := by
    unfold templateDistanceReadWork
    rw [size]
    gcongr
    exact (distanceTableReadWithSearchWork_spec G d).2
  obtain ⟨exactForest, simple, work⟩ := pairedTemplateEnumeratedWithWordWork_spec vertices label labelWork
    same cost G (templateReadWithWordWork n read) (templateReadWithWordWork n (fun d => read d.swap))
    (fun a b => by simpa only [templateReadWithWordWork,decide_eq_true_eq] using correct (b,a))
    (fun a b => by
      change decide ((read (a,b)).1 ≤ n) = true ↔ Reach (reverseArcs G) b a
      simpa only [decide_eq_true_eq,reach_reverseArcs] using correct (a,b))
    (templateDistanceReadWork n) (fun a b => readWork (b,a)) (fun a b => readWork (a,b))
    roots allRoots rootSimple height
  have count : roots.length = n := by
    have all : roots.toFinset = (Finset.univ : Finset V) := Finset.eq_univ_of_forall fun v =>
      List.mem_toFinset.mpr (allRoots v)
    rw [← List.toFinset_card_of_nodup rootSimple, all, Finset.card_univ, ← size]
  refine ⟨exactForest, simple, work.trans ?_⟩
  rw [count]
  dsimp only [heightForestListDistanceWorkPolynomial]
  gcongr <;> exact heightLexBlockCount_le_pow n height

/-- For indexed vertices the root list is generated once and vertex labels
are already the indices. -/
def finHeightForestListWithDistanceWork (n height : ℕ) (rows : List ((Fin n × Fin n) × ℕ)) :=
  withFinVerticesWithWordWork fun roots =>
    heightForestListWithDistanceWork n height (fun i => (i,1)) roots rows

local instance {n height : ℕ} : DecidableEq (HeightForestVertex (Fin n) height) :=
  (inferInstance : LinearOrder (HeightForestVertex (Fin n) height)).toDecidableEq

theorem finHeightForestListWithDistanceWork_spec {n : ℕ} (G : Arcs (Fin n)) (height : ℕ) :
    let out := finHeightForestListWithDistanceWork n height (distanceTableWithSearchWork G).1
    out.1.toFinset = heightForest G height ∧ out.1.Nodup ∧
      out.2 ≤ 8*n+5+heightForestListDistanceWorkPolynomial n height 1 := by
  have checked := withFinVerticesWithWordWork_spec
    (fun roots => heightForestListWithDistanceWork n height (fun i => (i,1)) roots (distanceTableWithSearchWork G).1)
    (heightForestListDistanceWorkPolynomial n height 1)
    (P := fun out => out.toFinset = heightForest G height ∧ out.Nodup)
    (fun roots distinct complete => by
      obtain ⟨same, simple, work⟩ := heightForestListWithDistanceWork_spec G (by simp)
        (Equiv.refl (Fin n)) (fun i => (i,1)) 1 (fun _ => rfl) (fun _ => le_rfl) roots complete distinct height
      exact ⟨⟨same,simple⟩,work⟩)
  exact ⟨checked.1.1, checked.1.2, checked.2.trans_eq (by omega)⟩

end OnlineReachabilityPreservers
