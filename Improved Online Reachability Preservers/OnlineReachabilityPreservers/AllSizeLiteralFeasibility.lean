import OnlineReachabilityPreservers.EssentialArcCount
import OnlineReachabilityPreservers.FrozenBoundaryCases
import OnlineReachabilityPreservers.FullThreeLiteralFeasibility
import OnlineReachabilityPreservers.SimplePaths

/-! The exact number of literal rows possible under full exclusion at every size. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

/-- If each selected arc has its own original row, a substitute route
would give a full bridge with those distinct original rows. -/
theorem distinct_list_steps_have_no_detours {n p : ℕ}
    (paths : Fin p → List (Fin n)) (all : ∀ d, IsEmpty (Bridge (Before paths) d))
    (arcs : Arcs (Fin n)) (owner : arcs → Fin p) (unique : Function.Injective owner)
    (compares : ∀ e : arcs, Before paths (owner e) e.val.1 e.val.2) :
    ∀ {u v : Fin n}, Edge arcs u v → ¬ Reach (arcs.erase (u,v)) u v := by
  intro u v on detour
  let river : arcs := ⟨(u,v),on⟩
  have apart : u ≠ v := listBefore_ne (compares river)
  obtain ⟨edges,found⟩ := routePath_succeeds.mpr detour
  have walk := routePath_some found
  have length : 2 ≤ edges.length := by
    cases edges with
    | nil =>
      have equal : u = v := by cases walk.1; rfl
      exact (apart equal).elim
    | cons e rest =>
      cases rest with
      | nil =>
        cases walk.1 with
        | cons edge empty =>
          cases empty
          exact ((mem_erase.mp edge).1 rfl).elim
      | cons f more => simp
  let d := edges.length-1
  have edgeCount : edges.length = d+1 := by dsimp [d]; omega
  let list := u::edges.map Prod.snd
  have vertexCount : list.length = d+2 := by simp [list,edgeCount]
  let vertex (i : Fin (d+2)) : Fin n := list[i.val]'(by rw [vertexCount]; exact i.isLt)
  have vertexListSimple : list.Nodup := by
    change (u::edges.map Prod.snd).Nodup
    rw [walk.1.vertex_list]
    exact walk.2
  have vertexUnique : Function.Injective vertex :=
    (List.nodup_iff_injective_getElem.mp vertexListSimple).comp (Fin.cast_injective vertexCount.symm)
  have first : vertex 0 = u := rfl
  have last : vertex (Fin.last (d+1)) = v := by
    unfold vertex list
    rw [List.getElem_of_eq walk.1.vertex_list]
    simp [List.getElem_append_right,edgeCount]
  let index (i : Fin (d+1)) : Fin edges.length := Fin.cast edgeCount.symm i
  have edgeOn (i : Fin (d+1)) : edges[(index i).val] ∈ arcs.erase (u,v) :=
    walk.1.mem (List.getElem_mem _)
  let arc (i : Fin (d+1)) : arcs := ⟨edges[(index i).val],(mem_erase.mp (edgeOn i)).2⟩
  have coordinates (i : Fin (d+1)) : (arc i).val = (vertex i.castSucc,vertex i.succ) := by
    apply Prod.ext
    · dsimp [arc,vertex,list,index]
      rw [List.getElem_of_eq walk.1.vertex_list]
      rw [List.getElem_append_left (by simpa only [List.length_map,edgeCount] using i.isLt),List.getElem_map]
    · simp [arc,vertex,list,index]
  have arcUnique : Function.Injective arc := by
    intro i j same
    have equal : vertex i.castSucc = vertex j.castSucc := by
      rw [← show (arc i).val.1 = vertex i.castSucc from congrArg Prod.fst (coordinates i),
        ← show (arc j).val.1 = vertex j.castSucc from congrArg Prod.fst (coordinates j),same]
    exact Fin.castSucc_injective _ (vertexUnique equal)
  apply (all d).false
  refine ⟨vertex,owner ∘ arc,owner river,vertexUnique,unique.comp arcUnique,?_,?_,?_⟩
  · intro i same
    have equal : (arc i).val = (u,v) := (congrArg Subtype.val (unique same)).symm
    exact (mem_erase.mp (edgeOn i)).1 equal
  · rw [first,last]
    exact compares river
  · intro i
    have compare := compares (arc i)
    rw [coordinates i] at compare
    exact compare

/-- Exclusion at every full size sharpens the cutoff-three upper bound
on the number of distinct nonempty simple rows. -/
theorem literal_full_all_path_count_le_tree_or_bipartite {n p : ℕ} (paths : Fin p → List (Fin n))
    (unique : Function.Injective paths) (well : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (all : ∀ d, IsEmpty (Bridge (Before paths) d)) : p ≤ n+max (2*(n-1)) (n^2/4) := by
  have halfTwo : HalfBridgeFree (Before paths) 2 := (show BridgeFree (Before paths) 2 from fun d _ => all d).halfFree
  obtain ⟨arcs,count,owner,ownerUnique,compares⟩ := literal_first_darts paths unique well halfTwo le_rfl
  have bound := essential_arcs_card_le_tree_or_bipartite arcs
    (fun {_ _} => distinct_list_steps_have_no_detours paths all arcs owner ownerUnique compares)
  rw [Fintype.card_fin] at bound
  exact count.trans (Nat.add_le_add_left bound _)

private theorem balanced_layers_product_eq_sq_div_four (n : ℕ) : (n/2)*(n-n/2) = n^2/4 := by
  let a := n/2
  let b := n-a
  have nEq : n = a+b := by dsimp [a,b]; omega
  have side : b = a ∨ b = a+1 := by dsimp [a,b]; omega
  change a*b = n^2/4
  rcases side with same | next
  · have expanded : (a+b)^2 = 4*(a*b) := by rw [same]; ring
    rw [nEq,expanded]
    omega
  · have expanded : (a+b)^2 = 4*(a*b)+1 := by rw [next]; ring
    rw [nEq,expanded]
    omega

/-- The exact all-size literal path capacity is the vertex count plus
whichever gives more pairs, the bidirectional star or the one-way
balanced bipartite graph. -/
theorem literal_full_all_feasible_iff {n p : ℕ} :
    (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before paths) d))) ↔
      p ≤ n+max (2*(n-1)) (n^2/4) := by
  constructor
  · rintro ⟨paths,unique,rows,all⟩
    exact literal_full_all_path_count_le_tree_or_bipartite paths unique rows all
  · intro enough
    by_cases star : n^2/4 ≤ 2*(n-1)
    · exact literal_full_all_star_rows (by simpa only [max_eq_left star] using enough)
    · have bound : p ≤ n+(n/2)*(n-n/2) := by
        rw [balanced_layers_product_eq_sq_div_four]
        simpa only [max_eq_right (le_of_not_ge star)] using enough
      let r := min p ((n/2)*(n-n/2))
      let s := p-r
      have singletonBudget : s ≤ n := by dsimp [s,r]; omega
      have rAddS : r+s = p := Nat.add_sub_of_le (min_le_left _ _)
      obtain ⟨paths,unique,rows,all,_⟩ := literal_full_all_short_rows (n := n) (min_le_right p _) singletonBudget
      have witness : ∃ paths : Fin (r+s) → List (Fin n), Function.Injective paths ∧
          (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ ∀ d, IsEmpty (Bridge (Before paths) d) :=
        ⟨paths,unique,rows,all⟩
      exact rAddS ▸ witness

/-- A finite full cutoff covering one whole budget has the same exact
literal feasibility threshold as all-size full exclusion. -/
theorem literal_full_feasible_iff_of_cutoff_ge_min {n p cutoff : ℕ} (covers : min n p ≤ cutoff) :
    (∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff) ↔
      p ≤ n+max (2*(n-1)) (n^2/4) := by
  rw [← literal_full_all_feasible_iff]
  constructor
  · rintro ⟨paths,unique,rows,free⟩
    exact ⟨paths,unique,rows,bridgeFree_all_of_cutoff_ge_min free covers⟩
  · rintro ⟨paths,unique,rows,free⟩
    exact ⟨paths,unique,rows,fun d _ => free d⟩

end OnlineReachabilityPreservers
