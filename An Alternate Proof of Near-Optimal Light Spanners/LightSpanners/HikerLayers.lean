import LightSpanners.HikerSquads
import LightSpanners.CycleSegments
import Mathlib.Algebra.Order.Floor.Semiring

namespace LightSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : UnitSpanningCycle G w)

namespace WalkSquad

noncomputable def forwardStep : WalkSquad G :=
  ⟨C.successor,fun v => .cons (C.successor_adj v) .nil⟩

/-- Layer zero hikes before any shuttle move. Each later layer first moves
one step forward, then processes all chords. Thus t shuttle steps support t+1
chord layers, including the essential zero-shuttle case. -/
noncomputable def morning (ds : List G.Dart) : ℕ → WalkSquad G
  | 0 => edgeLayer ds
  | t+1 => (morning ds t).trans ((forwardStep C).trans (edgeLayer ds))

theorem edgeLayer_cycleDarts (ds : List G.Dart) (v : V)
    (hd : ∀ d ∈ ds, d.edge ∉ C.cycle.edges) :
    C.cycleDarts ((edgeLayer ds).path v) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro d hm
  have he : d.edge ∈ ((edgeLayer ds).path v).edges := List.mem_map.mpr ⟨d,hm,rfl⟩
  obtain ⟨e,hed,hee⟩ := List.mem_map.mp ((edgeLayer_edges_sublist ds v).subset he)
  have hn := hd e hed
  simpa [hee] using hn

theorem morning_cycle_count (ds : List G.Dart) (v : V)
    (hd : ∀ d ∈ ds, d.edge ∉ C.cycle.edges) (t : ℕ) :
    (C.cycleDarts ((morning C ds t).path v)).length = t := by
  induction t generalizing v with
  | zero => simp [morning,edgeLayer_cycleDarts C ds v hd]
  | succ t ih =>
    change (C.cycleDarts (((morning C ds t).path v).append
      ((Walk.cons (C.successor_adj _) .nil).append ((edgeLayer ds).path _)))).length = t+1
    rw [C.cycleDarts_append,C.cycleDarts_append,List.length_append,List.length_append,ih,
      edgeLayer_cycleDarts C ds _ hd,List.length_nil]
    have hm : s((morning C ds t).position v,C.successor ((morning C ds t).position v)) ∈ C.cycle.edges :=
      List.mem_map.mpr ⟨_,C.successor_dart _,rfl⟩
    simp [UnitSpanningCycle.cycleDarts,hm]

theorem morning_cycle_forward (ds : List G.Dart) (v : V)
    (hd : ∀ d ∈ ds, d.edge ∉ C.cycle.edges) (t : ℕ) :
    ∀ d ∈ C.cycleDarts ((morning C ds t).path v), d ∈ C.cycle.darts := by
  induction t generalizing v with
  | zero => simp [morning,edgeLayer_cycleDarts C ds v hd]
  | succ t ih =>
    change ∀ d ∈ C.cycleDarts (((morning C ds t).path v).append
      ((Walk.cons (C.successor_adj _) .nil).append ((edgeLayer ds).path _))), _
    rw [C.cycleDarts_append,C.cycleDarts_append,edgeLayer_cycleDarts C ds _ hd,List.append_nil]
    intro d he
    rw [List.mem_append] at he
    rcases he with he | he
    · exact ih v d he
    · have he' : d ∈ (Walk.cons (C.successor_adj ((morning C ds t).position v)) .nil).darts :=
        (List.mem_filter.mp he).1
      have heq : d = ⟨((morning C ds t).position v,C.successor ((morning C ds t).position v)),C.successor_adj _⟩ := by
        simpa only [Walk.darts_cons,Walk.darts_nil,List.mem_singleton] using he'
      rw [heq]
      exact C.successor_dart _

/-- Two adjacent forward cycle darts cannot be the same undirected edge. -/
theorem forward_darts_ne {d e : G.Dart} (hd : d ∈ C.cycle.darts)
    (he : e ∈ C.cycle.darts) (hadj : G.DartAdj d e) : d.edge ≠ e.edge := by
  intro heq
  have hde : d = e := List.inj_on_of_nodup_map C.hamiltonian.isCycle.isTrail.edges_nodup hd he heq
  subst e
  exact d.adj.ne hadj.symm

/-- A forward shuttle step cannot backtrack the preceding morning step. -/
theorem nonbacktracking_concat_forward {u v : V} (p : G.Walk u v)
    (hp : p.edges.IsChain (· ≠ ·))
    (hforward : ∀ d ∈ C.cycleDarts p, d ∈ C.cycle.darts) :
    (p.concat (C.successor_adj v)).edges.IsChain (· ≠ ·) := by
  apply (List.isChain_map Dart.edge).mpr
  rw [Walk.darts_concat,List.concat_eq_append]
  have hchain := (p.concat (C.successor_adj v)).isChain_dartAdj_darts
  rw [Walk.darts_concat,List.concat_eq_append] at hchain
  apply List.IsChain.append ((List.isChain_map Dart.edge).mp hp) (by simp)
  intro d hd e he
  have heq : e = ⟨(v,C.successor v),C.successor_adj v⟩ := by simpa [eq_comm] using he
  subst e
  have hadj : G.DartAdj d ⟨(v,C.successor v),C.successor_adj v⟩ :=
    (List.isChain_append.mp hchain).2.2 d hd _ he
  intro hedge
  have hmem : d ∈ C.cycleDarts p := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_of_mem_getLast? hd,?_⟩
    have hm : (⟨(v,C.successor v),C.successor_adj v⟩ : G.Dart).edge ∈ C.cycle.edges :=
      List.mem_map.mpr ⟨_,C.successor_dart v,rfl⟩
    simpa [hedge] using hm
  exact forward_darts_ne C (hforward d hmem) (C.successor_dart v) hadj hedge

theorem edgeLayer_nonbacktracking (ds : List G.Dart) (v : V)
    (hds : (ds.map Dart.edge).Nodup) : ((edgeLayer ds).path v).edges.IsChain (· ≠ ·) := by
  have hn := hds.sublist (edgeLayer_edges_sublist ds v)
  exact (show List.Pairwise (· ≠ ·) ((edgeLayer ds).path v).edges from hn).isChain

/-- Every actual morning walk is non-backtracking, including empty chord
layers and consecutive forward shuttle moves. -/
theorem morning_nonbacktracking (ds : List G.Dart) (v : V)
    (hds : (ds.map Dart.edge).Nodup) (hd : ∀ d ∈ ds, d.edge ∉ C.cycle.edges)
    (t : ℕ) : ((morning C ds t).path v).edges.IsChain (· ≠ ·) := by
  induction t generalizing v with
  | zero => exact edgeLayer_nonbacktracking ds v hds
  | succ t ih =>
    let p := (morning C ds t).path v
    let v' := C.successor ((morning C ds t).position v)
    let q := (edgeLayer ds).path v'
    change (p.append ((Walk.cons (C.successor_adj _) .nil).append q)).edges.IsChain (· ≠ ·)
    rw [Walk.cons_nil_append,← Walk.concat_append,Walk.edges_append]
    apply List.IsChain.append
      (nonbacktracking_concat_forward C p (ih v) (morning_cycle_forward C ds v hd t))
      (edgeLayer_nonbacktracking ds v' hds)
    intro e he f hf heq
    have he' : e = s((morning C ds t).position v,v') := by
      simpa [Walk.edges_concat,List.concat_eq_append,eq_comm,v'] using he
    have hf' : f ∈ q.edges := List.mem_of_mem_head? hf
    obtain ⟨d,hdd,hdf⟩ := List.mem_map.mp ((edgeLayer_edges_sublist ds v').subset hf')
    have hn := hd d hdd
    apply hn
    have hm : s((morning C ds t).position v,v') ∈ C.cycle.edges :=
      List.mem_map.mpr ⟨_,C.successor_dart _,rfl⟩
    simpa [hdf,← heq,he'] using hm

variable [Fintype V]

@[simp] theorem totalChords_forwardStep : totalChords C (forwardStep C) = 0 := by
  unfold totalChords
  apply sum_eq_zero
  intro v _
  have hm : s(v,C.successor v) ∈ C.cycle.edges := List.mem_map.mpr ⟨_,C.successor_dart v,rfl⟩
  simp [forwardStep,UnitSpanningCycle.chordEdges,hm]

/-- Exact total morning traversals, with no floor approximation. -/
theorem totalChords_morning (ds : List G.Dart)
    (hd : ∀ d ∈ ds, d.edge ∉ C.cycle.edges) (t : ℕ) :
    totalChords C (morning C ds t) = 2*(t+1)*ds.length := by
  induction t with
  | zero => simp [morning,totalChords_edgeLayer C ds hd]
  | succ t ih =>
    rw [morning,totalChords_trans,totalChords_trans,totalChords_forwardStep,
      totalChords_edgeLayer C ds hd,ih]
    ring

end WalkSquad

/-- The repaired layer count is valid even when the extra-safe shuttle budget
is below one. This is the range omitted by 2 floor(x) ≥ x. -/
theorem floor_plus_one_layer_bound {eps W : ℝ} {k i : ℕ}
    (heps : 0 < eps) (hk : 0 < k) (hW : W < (2:ℝ)^(i+1)) :
    eps*k*W/4 ≤ 2*((⌊eps*k*2^i/2⌋₊ : ℕ)+1) := by
  have hkp : (0:ℝ) < k := by exact_mod_cast hk
  have hfloor := Nat.lt_floor_add_one (eps*k*2^i/2)
  have hweight := mul_lt_mul_of_pos_left hW (mul_pos heps hkp)
  have hx : 0 < eps*k*2^i := by positivity
  rw [pow_succ] at hweight
  nlinarith

end LightSpanners
