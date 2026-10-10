import LightSpanners.TourCycle
import Mathlib.Algebra.Group.Equiv.Defs

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Positions of the actual chosen Hamiltonian cycle, with a syntactically
nondegenerate modulus so its successor and predecessor are total. -/
abbrev Position := Fin (C.cycle.length - 3 + 3)

theorem cycle_length_position : C.cycle.length = C.cycle.length - 3 + 3 := by
  have := C.hamiltonian.isCycle.three_le_length
  omega

def positionHom : cycleGraph (C.cycle.length - 3 + 3) →g G :=
  LightSpanners.closedWalkCycleHom C.cycle C.cycle_length_position

theorem positionHom_bijective : Function.Bijective C.positionHom := by
  constructor
  · intro a b hab
    apply Fin.ext
    apply C.hamiltonian.isCycle.getVert_injOn'
      (by change a.val ≤ C.cycle.length-1; have := a.isLt; have := C.cycle_length_position; omega)
      (by change b.val ≤ C.cycle.length-1; have := b.isLt; have := C.cycle_length_position; omega)
    exact hab
  · exact LightSpanners.closedWalkCycleHom_surjective C.cycle C.cycle_length_position
      C.hamiltonian.mem_support

noncomputable def positionEquiv : C.Position ≃ V :=
  Equiv.ofBijective C.positionHom C.positionHom_bijective

@[simp] theorem positionEquiv_apply (i : C.Position) :
    C.positionEquiv i = C.cycle.getVert i.val := rfl

/-- The actual forward cycle step is a permutation of all vertices. -/
noncomputable def successor : Equiv.Perm V :=
  (C.positionEquiv.symm.trans (Equiv.addRight 1)).trans C.positionEquiv

@[simp] theorem successor_position (i : C.Position) :
    C.successor (C.positionEquiv i) = C.positionEquiv (i+1) := by
  change C.positionEquiv (C.positionEquiv.symm (C.positionEquiv i) + 1) = _
  rw [Equiv.symm_apply_apply]

theorem successor_adj (v : V) : G.Adj v (C.successor v) := by
  obtain ⟨i,rfl⟩ := C.positionEquiv.surjective v
  rw [C.successor_position]
  exact LightSpanners.closed_walk_getVert_add_one C.cycle C.cycle_length_position i

theorem position_add_one (i : C.Position) :
    C.positionEquiv (i+1) = C.cycle.getVert (i.val+1) := by
  rw [C.positionEquiv_apply]
  by_cases hi : i.val+1 = C.cycle.length-3+3
  · have hv : (i+1 : C.Position).val = 0 := by simp [Fin.val_add,hi]
    rw [hv, Walk.getVert_zero, hi, ← C.cycle_length_position, Walk.getVert_length]
  · have hv : (i+1 : C.Position).val = i.val+1 := by
      have hlt : i.val+1 < C.cycle.length-3+3 := by have := i.isLt; omega
      simp [Position, Fin.val_add, Nat.mod_eq_of_lt hlt]
    rw [hv]

theorem successor_dart (v : V) :
    (⟨(v,C.successor v), C.successor_adj v⟩ : G.Dart) ∈ C.cycle.darts := by
  obtain ⟨i,rfl⟩ := C.positionEquiv.surjective v
  have hi : i.val < C.cycle.darts.length := by
    rw [Walk.length_darts]
    have := i.isLt
    have := C.cycle_length_position
    omega
  have hd := List.getElem_mem (l := C.cycle.darts) hi
  rw [Walk.darts_getElem_eq_getVert] at hd
  have hstep := (C.successor_position i).trans (C.position_add_one i)
  convert hd using 1
  apply Dart.ext
  exact Prod.ext rfl hstep

/-- Membership in the cycle's actual directed edge list is precisely a
forward successor step, rather than an arbitrary chosen orientation. -/
theorem dart_mem_iff_successor (d : G.Dart) :
    d ∈ C.cycle.darts ↔ C.successor d.fst = d.snd := by
  constructor
  · intro hd
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hd
    have hi' : i < C.cycle.length-3+3 := by
      rw [Walk.length_darts] at hi
      have := C.cycle_length_position
      omega
    let j : C.Position := ⟨i,hi'⟩
    rw [Walk.darts_getElem_eq_getVert]
    change C.successor (C.positionEquiv j) = C.cycle.getVert (i+1)
    exact (C.successor_position j).trans (C.position_add_one j)
  · intro hd
    have heq : d = ⟨(d.fst,C.successor d.fst),C.successor_adj d.fst⟩ := by
      apply Dart.ext
      simp [hd]
    rw [heq]
    exact C.successor_dart d.fst


/-- A cycle does not contain both orientations of one edge. -/
theorem dart_reverse_not_mem {d : G.Dart} (hd : d ∈ C.cycle.darts) :
    d.symm ∉ C.cycle.darts := by
  intro hr
  have he : d.symm = d := List.inj_on_of_nodup_map C.hamiltonian.isCycle.isTrail.edges_nodup
    hr hd d.edge_symm
  exact d.symm_ne he

theorem edge_mem_iff_dart (d : G.Dart) :
    d.edge ∈ C.cycle.edges ↔ d ∈ C.cycle.darts ∨ d.symm ∈ C.cycle.darts := by
  rw [Walk.edges_eq_map_darts, List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    rcases (dart_edge_eq_iff a d).mp he with he | he
    · exact Or.inl (he ▸ ha)
    · exact Or.inr (he ▸ ha)
  · rintro (hd | hd)
    · exact ⟨d,hd,rfl⟩
    · exact ⟨d.symm,hd,d.edge_symm⟩

theorem predecessor_adj (v : V) : G.Adj v (C.successor.symm v) := by
  simpa using (C.successor_adj (C.successor.symm v)).symm

/-- An actual forward walk of any prescribed number of cycle steps. -/
noncomputable def forwardWalk : (n : ℕ) → (v : V) →
    G.Walk v ((C.successor : V → V)^[n] v)
  | 0, _ => .nil
  | n+1, v => .cons (C.successor_adj v) (forwardWalk n (C.successor v))

/-- An actual backward walk of any prescribed number of cycle steps. -/
noncomputable def backwardWalk : (n : ℕ) → (v : V) →
    G.Walk v ((C.successor.symm : V → V)^[n] v)
  | 0, _ => .nil
  | n+1, v => .cons (C.predecessor_adj v) (backwardWalk n (C.successor.symm v))

@[simp] theorem forwardWalk_length (n : ℕ) (v : V) : (C.forwardWalk n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [forwardWalk,ih]

@[simp] theorem backwardWalk_length (n : ℕ) (v : V) : (C.backwardWalk n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [backwardWalk,ih]

theorem forwardWalk_darts (n : ℕ) (v : V) :
    ∀ d ∈ (C.forwardWalk n v).darts, d ∈ C.cycle.darts := by
  induction n generalizing v with
  | zero => simp [forwardWalk]
  | succ n ih =>
    intro d hd
    change d ∈ (⟨(v,C.successor v),C.successor_adj v⟩ : G.Dart) ::
      (C.forwardWalk n (C.successor v)).darts at hd
    rw [List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact C.successor_dart v
    · exact ih _ d hd

theorem backwardWalk_darts (n : ℕ) (v : V) :
    ∀ d ∈ (C.backwardWalk n v).darts, d.symm ∈ C.cycle.darts := by
  induction n generalizing v with
  | zero => simp [backwardWalk]
  | succ n ih =>
    intro d hd
    change d ∈ (⟨(v,C.successor.symm v),C.predecessor_adj v⟩ : G.Dart) ::
      (C.backwardWalk n (C.successor.symm v)).darts at hd
    rw [List.mem_cons] at hd
    rcases hd with rfl | hd
    · apply (C.dart_mem_iff_successor _).mpr
      exact C.successor.apply_symm_apply v
    · exact ih _ d hd

end LightSpanners.UnitSpanningCycle
