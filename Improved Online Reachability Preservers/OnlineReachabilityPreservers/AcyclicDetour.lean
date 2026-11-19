import OnlineReachabilityPreservers.IntersectionOrder

/-! Shorten a detour in a common vertex order while preserving its final path. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I]

inductive OrderedDetour (paths : I → Finset V) (river : I) :
    V → V → List I → Prop
  | nil (u : V) : OrderedDetour paths river u u []
  | cons {u v w : V} {c : I} {C : List I} (fresh : river ≠ c)
      (edge : PathBefore paths c u v) (tail : OrderedDetour paths river v w C) :
      OrderedDetour paths river u w (c::C)

namespace OrderedDetour

variable {paths : I → Finset V} {river : I} {u v w : V} {C : List I}

omit [LinearOrder I] in
theorem append_step (r : OrderedDetour paths river u v C) {c : I}
    (fresh : river ≠ c) (edge : PathBefore paths c v w) :
    OrderedDetour paths river u w (C++[c]) := by
  induction r with
  | nil => exact .cons fresh edge (.nil _)
  | cons diff e _ ih => exact .cons diff e (ih edge)

omit [LinearOrder I] in
private theorem used_fresh (r : OrderedDetour paths river u v C) {c : I} (mem : c ∈ C) :
    river ≠ c := by
  induction r with
  | nil => simp at mem
  | cons diff _ _ ih =>
    rcases List.mem_cons.mp mem with rfl | h
    · exact diff
    · exact ih h

omit [LinearOrder I] in
private theorem suffix_after (r : OrderedDetour paths river u v C) (nodup : C.Nodup)
    {c : I} (present : c ∈ C) :
    ∃ a b D, u ≤ a ∧ PathBefore paths c a b ∧ OrderedDetour paths river b v D ∧
      D.Nodup ∧ c ∉ D ∧ (c::D) <:+ C := by
  induction r with
  | nil => simp at present
  | @cons x y z d D fresh edge tail ih =>
    obtain ⟨none,nd⟩ := List.nodup_cons.mp nodup
    rcases List.mem_cons.mp present with rfl | mem
    · exact ⟨x,y,D,le_rfl,edge,tail,nd,none,List.suffix_rfl⟩
    · obtain ⟨a,b,E,le,other,rest,ndE,noE,ending⟩ := ih nd mem
      exact ⟨a,b,E,edge.2.2.le.trans le,other,rest,ndE,noE,ending.trans (List.suffix_cons _ _)⟩

/-- A repeated colour can be shortcut when every path uses the same vertex order. -/
private theorem remove_duplicates (r : OrderedDetour paths river u v C) :
    ∃ D : List I, OrderedDetour paths river u v D ∧ D.Nodup ∧
      D.length ≤ C.length ∧ D.getLast? = C.getLast? := by
  induction r with
  | nil => exact ⟨[],.nil _,by simp⟩
  | @cons s t v c C fresh edge tail ih =>
    obtain ⟨D,shortened,nd,length,last⟩ := ih
    by_cases used : c ∈ D
    · obtain ⟨a,b,E,ha,other,rest,ndE,noE,ending⟩ := suffix_after shortened nd used
      have step : PathBefore paths c s b :=
        ⟨edge.1,other.2.1,(edge.2.2.trans_le ha).trans other.2.2⟩
      have d_ne : D ≠ [] := List.ne_nil_of_mem used
      have c_ne : C ≠ [] := by
        intro e
        simp [e] at last
        exact d_ne last
      refine ⟨c::E,.cons fresh step rest,List.nodup_cons.mpr ⟨noE,ndE⟩,
        (ending.length_le.trans length).trans (Nat.le_succ _),?_⟩
      obtain ⟨before,eq⟩ := ending
      rw [List.getLast?_cons_of_ne_nil c_ne, ← last, ← eq, List.getLast?_append_of_ne_nil _ (by simp)]
    · refine ⟨c::D,.cons fresh edge shortened,List.nodup_cons.mpr ⟨used,nd⟩,
        Nat.succ_le_succ length,?_⟩
      simp only [List.getLast?_cons, last]

omit [LinearOrder I] in
private theorem coordinates (r : OrderedDetour paths river u v C) :
    ∃ x : Fin (C.length+1) → V, x 0 = u ∧ x (Fin.last C.length) = v ∧
      ∀ i : Fin C.length, PathBefore paths (C.get i) (x i.castSucc) (x i.succ) := by
  induction r with
  | nil =>
    exact ⟨fun _ => _,rfl,rfl,fun i => i.elim0⟩
  | @cons s t v c D _ edge tail ih =>
    obtain ⟨x,x0,xlast,steps⟩ := ih
    let vertices : Fin ((c::D).length+1) → V := Fin.cases s x
    refine ⟨vertices,rfl,?_,?_⟩
    · change x (Fin.last D.length) = v
      exact xlast
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j,rfl⟩
      · change PathBefore paths c s (x 0)
        rwa [x0]
      · change PathBefore paths (D.get j) (x j.castSucc) (x j.succ)
        exact steps j

private theorem witness_preserving_last (r : OrderedDetour paths river u v C)
    (riverEdge : PathBefore paths river u v) :
    ∃ k : ℕ, k+1 ≤ C.length ∧ ∃ b : Bridge (PathBefore paths) k,
      b.river = river ∧ some (b.arc (Fin.last k)) = C.getLast? := by
  obtain ⟨D,short,nd,length,last⟩ := remove_duplicates r
  obtain ⟨x,x0,xlast,steps⟩ := short.coordinates
  cases D with
  | nil => exact (riverEdge.2.2.ne (x0.symm.trans xlast)).elim
  | cons c rest =>
    let b : Bridge (PathBefore paths) rest.length :=
      orderedBridge x (fun i => (c::rest).get i) river
        (List.nodup_iff_injective_get.mp nd) (fun i => short.used_fresh ((c::rest).get_mem i))
        (by
          change PathBefore paths river (x 0) (x (Fin.last (c::rest).length))
          rwa [x0,xlast]) steps
    have outputLast : (c::rest).getLast? = some ((c::rest).get (Fin.last rest.length)) := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp)]
      rfl
    exact ⟨rest.length,length,b,rfl,outputLast.symm.trans last⟩

theorem yields_bridge (r : OrderedDetour paths river u v C)
    (riverEdge : PathBefore paths river u v) : ∃ k, Nonempty (Bridge (PathBefore paths) k) := by
  obtain ⟨k,_,bridge,_,_⟩ := witness_preserving_last r riverEdge
  exact ⟨k,⟨bridge⟩⟩

omit [LinearOrder I] in
private theorem of_indexed {paths : I → Finset V} {river : I} :
    ∀ {n : ℕ} (v : Fin (n+1) → V) (a : Fin n → I),
      (∀ i, river ≠ a i) → (∀ i, PathBefore paths (a i) (v i.castSucc) (v i.succ)) →
      OrderedDetour paths river (v 0) (v (Fin.last n)) (List.ofFn a) := by
  intro n
  induction n with
  | zero =>
    intro v a _ _
    rw [List.ofFn_zero, show Fin.last 0 = 0 by exact Fin.ext rfl]
    exact .nil _
  | succ n ih =>
    intro v a fresh steps
    rw [List.ofFn_succ]
    apply OrderedDetour.cons (fresh 0) (steps 0)
    exact ih (v ∘ Fin.succ) (a ∘ Fin.succ) (fun i => fresh i.succ) (fun i => steps i.succ)

/-- Compress an ordered detour without changing its endpoints or its last path. -/
theorem shorten_indexed {paths : I → Finset V} {k : ℕ}
    (v : Fin (k+2) → V) (a : Fin (k+1) → I) (r : I)
    (different : ∀ i, r ≠ a i)
    (riverEdge : PathBefore paths r (v 0) (v (Fin.last (k+1))))
    (step : ∀ i, PathBefore paths (a i) (v i.castSucc) (v i.succ)) :
    ∃ j ≤ k, ∃ bridge : Bridge (PathBefore paths) j,
      bridge.river = r ∧ bridge.arc (Fin.last j) = a (Fin.last k) := by
  obtain ⟨j,length,bridge,river,last⟩ :=
    witness_preserving_last (of_indexed v a different step) riverEdge
  rw [List.length_ofFn] at length
  have inputLast : (List.ofFn a).getLast? = some (a (Fin.last k)) := by
    rw [List.ofFn_succ_last]
    simp
  exact ⟨j,by omega,bridge,river,Option.some.inj (last.trans inputLast)⟩

end OrderedDetour

end OnlineReachabilityPreservers
