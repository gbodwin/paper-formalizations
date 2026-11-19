import OnlineReachabilityPreservers.CyclicIntersections

/-! Removing repeated vertices in a projected chain of distinct paths. -/

namespace OnlineReachabilityPreservers

private inductive LabeledWalk {V I : Type*} (before : I → V → V → Prop) :
    V → V → List (I × V) → Prop
  | nil (u : V) : LabeledWalk before u u []
  | cons {u v w : V} {i : I} {rest : List (I × V)} (edge : before i u v)
      (tail : LabeledWalk before v w rest) : LabeledWalk before u w ((i,v)::rest)

namespace LabeledWalk

variable {V I : Type*} {before : I → V → V → Prop}

private theorem suffixFrom {u v x : V} {E : List (I × V)} (walk : LabeledWalk before u v E)
    (present : x ∈ u :: E.map Prod.snd) :
    ∃ F, F <:+ E ∧ LabeledWalk before x v F ∧ (x :: F.map Prod.snd) <:+ (u :: E.map Prod.snd) := by
  induction walk with
  | nil a =>
    simp only [List.map_nil, List.mem_singleton] at present
    subst x
    exact ⟨[], List.suffix_rfl, .nil _, List.suffix_rfl⟩
  | @cons y z w i D step tail ih =>
    rcases List.mem_cons.mp present with rfl | next
    · exact ⟨_, List.suffix_rfl, .cons step tail, List.suffix_rfl⟩
    · obtain ⟨F, suffix, subwalk, vertices⟩ := ih next
      exact ⟨F, suffix.trans (List.suffix_cons _ _), subwalk, vertices.trans (List.suffix_cons _ _)⟩

/-- Erase closed sections while keeping a subsequence of the original edges. -/
private theorem eraseCycles {u v : V} {E : List (I × V)} (walk : LabeledWalk before u v E) :
    ∃ F, F.Sublist E ∧ LabeledWalk before u v F ∧ (u :: F.map Prod.snd).Nodup := by
  induction walk with
  | nil a => exact ⟨[], List.Sublist.refl _, .nil _, by simp⟩
  | @cons x y z i D edge tail ih =>
    classical
    obtain ⟨F, sub, short, distinct⟩ := ih
    by_cases occurs : x ∈ y :: F.map Prod.snd
    · obtain ⟨Q, suffix, walk, vertices⟩ := suffixFrom short occurs
      exact ⟨Q, suffix.sublist.trans (sub.trans (List.sublist_cons_self _ _)), walk, vertices.sublist.nodup distinct⟩
    · exact ⟨(i,y)::F, sub.cons_cons _, .cons edge short, List.nodup_cons.mpr ⟨occurs,distinct⟩⟩

private theorem ofIndexed : ∀ {n : ℕ} (v : Fin (n+1) → V) (a : Fin n → I),
    (∀ i, before (a i) (v i.castSucc) (v i.succ)) →
    LabeledWalk before (v 0) (v (Fin.last n)) (List.ofFn fun i => (a i,v i.succ)) := by
  intro n
  induction n with
  | zero =>
    intro v a _
    rw [List.ofFn_zero, show Fin.last 0 = 0 by exact Fin.ext rfl]
    exact .nil _
  | succ n ih =>
    intro v a steps
    rw [List.ofFn_succ]
    apply LabeledWalk.cons (steps 0)
    exact ih (v ∘ Fin.succ) (a ∘ Fin.succ) (fun i => steps i.succ)

private def indexedVertex (u : V) (E : List (I × V)) (i : Fin (E.length+1)) : V :=
  (u :: E.map Prod.snd).get (Fin.cast (by simp) i)

private theorem indexedVertex_inj {u : V} {E : List (I × V)} (nodup : (u :: E.map Prod.snd).Nodup) :
    Function.Injective (indexedVertex u E) :=
  (List.nodup_iff_injective_get.mp nodup).comp (Fin.cast_injective _)

private theorem indexed {u v : V} {E : List (I × V)} (walk : LabeledWalk before u v E) :
    indexedVertex u E 0 = u ∧ indexedVertex u E (Fin.last E.length) = v ∧
      ∀ i : Fin E.length, before (E.get i).1 (indexedVertex u E i.castSucc) (indexedVertex u E i.succ) := by
  induction walk with
  | nil a => exact ⟨rfl,rfl,fun i => i.elim0⟩
  | @cons x y z i D edge tail ih =>
    obtain ⟨_, last, steps⟩ := ih
    refine ⟨rfl,last,?_⟩
    intro j
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k,rfl⟩
    · exact edge
    · exact steps k

end LabeledWalk

/-- Project vertices without requiring global injectivity. Erasing closed sections
may shorten the bridge and drops some arcs, while keeping its river. -/
theorem Bridge.project_vertices {V W I : Type*} {before : I → V → V → Prop} {after : I → W → W → Prop}
    {k : ℕ} (b : Bridge before k) (project : V → W)
    (steps : ∀ {i x y}, before i x y → after i (project x) (project y))
    (strict : ∀ {i x y}, after i x y → x ≠ y) :
    ∃ j ≤ k, ∃ short : Bridge after j, short.river = b.river := by
  let v := project ∘ b.vertex
  let E := List.ofFn fun i => (b.arc i, v i.succ)
  have walk : LabeledWalk after (v 0) (v (Fin.last (k+1))) E :=
    LabeledWalk.ofIndexed v b.arc (fun i => steps (b.arcStep i))
  obtain ⟨F, sub, short, vertices⟩ := walk.eraseCycles
  have colorBefore : E.map Prod.fst = List.ofFn b.arc := by simp [E, List.map_ofFn, Function.comp_def]
  have distinct : (F.map Prod.fst).Nodup := by
    apply (sub.map Prod.fst).nodup
    rw [colorBefore, List.nodup_ofFn]
    exact b.distinctArcs
  have fresh {x : I} (hx : x ∈ F.map Prod.fst) : b.river ≠ x := by
    have h := (sub.map Prod.fst).subset hx
    rw [colorBefore, List.mem_ofFn] at h
    obtain ⟨i,rfl⟩ := h
    exact b.river_ne_arc i
  obtain ⟨start, last, projected⟩ := short.indexed
  cases F with
  | nil =>
    exact (strict (steps b.riverStep) (start.symm.trans last)).elim
  | cons e tail =>
    let x := LabeledWalk.indexedVertex (v 0) (e::tail)
    let index (i : Fin (tail.length+1)) := ((e::tail).get i).1
    have injective : Function.Injective index := by
      intro i j equal
      have indexEq : ∀ q : Fin (tail.length+1), ((e::tail).map Prod.fst).get (Fin.cast (by simp) q) = index q := by
        intro q
        simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast, index]
      have same := (List.nodup_iff_injective_get.mp distinct) ((indexEq i).trans (equal.trans (indexEq j).symm))
      exact Fin.cast_injective _ same
    have riverAbsent (i : Fin (tail.length+1)) : b.river ≠ index i :=
      fresh (List.mem_map_of_mem ((e::tail).get_mem i))
    refine ⟨tail.length,?_,⟨x,index,b.river, LabeledWalk.indexedVertex_inj vertices,injective,riverAbsent,?_,projected⟩,rfl⟩
    · have bound := sub.length_le
      simpa [E] using Nat.le_of_succ_le_succ (show tail.length+1 ≤ k+1 by simpa [E] using bound)
    · change after b.river (x 0) (x (Fin.last (tail.length+1)))
      rw [show x 0 = v 0 from start, show x (Fin.last (tail.length+1)) = v (Fin.last (k+1)) from last]
      exact steps b.riverStep

end OnlineReachabilityPreservers
