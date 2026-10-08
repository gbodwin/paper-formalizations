import LinearDistancePreservers.ConsistentTiebreaking
import LinearDistancePreservers.Branching

/-! Extract the exact predecessor/rank data used by the branching bound
from the optimal paths constructed in `ConsistentTiebreaking`. -/
namespace LinearDistancePreservers.ConsistentTiebreaking
open SimpleGraph
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [DecidableEq V] {K : SimpleGraph V}

noncomputable def predecessor {s t : V} (p : K.Walk s t) (v : V) : Option V :=
  if h : ∃ d ∈ p.darts, d.snd = v then some h.choose.fst else none

theorem incoming_unique {s t : V} {p : K.Walk s t} (hp : p.IsPath)
    {d e : K.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts) (hs : d.snd = e.snd) : d = e := by
  have hn : (p.darts.map (fun d => d.snd)).Nodup := by
    rw [Walk.map_snd_darts]
    exact hp.support_nodup.tail
  exact List.inj_on_of_nodup_map hn hd he hs

theorem predecessor_of_dart {s t : V} {p : K.Walk s t} (hp : p.IsPath)
    {d : K.Dart} (hd : d ∈ p.darts) : predecessor p d.snd = some d.fst := by
  classical
  have hex : ∃ e ∈ p.darts, e.snd = d.snd := ⟨d,hd,rfl⟩
  rw [predecessor, dif_pos hex]
  have heq : hex.choose = d := incoming_unique hp hex.choose_spec.1 hd hex.choose_spec.2
  rw [heq]

theorem predecessor_some_iff {s t : V} {p : K.Walk s t} (hp : p.IsPath) {u v : V} :
    predecessor p v = some u ↔ ∃ d ∈ p.darts, d.fst = u ∧ d.snd = v := by
  classical
  constructor
  · intro he
    unfold predecessor at he
    split at he
    next h => exact ⟨h.choose, h.choose_spec.1, Option.some.inj he, h.choose_spec.2⟩
    next h => cases he
  · rintro ⟨d,hd,rfl,rfl⟩
    exact predecessor_of_dart hp hd

theorem predecessor_mem {s t : V} {p : K.Walk s t} {v : V}
    (h : predecessor p v ≠ none) : v ∈ p.support := by
  classical
  unfold predecessor at h
  split at h
  next h' =>
    obtain ⟨d,hd,rfl⟩ := h'
    exact p.dart_snd_mem_support_of_mem_darts hd
  next h' => exact (h rfl).elim

/-- The predecessor at the end of any nonempty subwalk is the predecessor
on the whole simple path. -/
theorem predecessor_subwalk_end {s t a b : V} {p : K.Walk s t}
    (hp : p.IsPath) {q : K.Walk a b} (hsub : q.IsSubwalk p) (hne : a ≠ b) :
    predecessor p b = some q.penultimate := by
  have hnil : ¬ q.Nil := by intro h; cases h; exact hne rfl
  exact predecessor_of_dart hp (hsub.darts_subset (q.lastDart_mem_darts hnil))

theorem consistent_predecessors {G : V → V → Prop} {w : V → V → ℝ≥0}
    {s t s' t' v z : V} {p : K.Walk s t} {p' : K.Walk s' t'}
    (hp : Optimal G w p) (hp' : Optimal G w p')
    (hv : v ∈ p.support) (hz : z ∈ p.support)
    (hv' : v ∈ p'.support) (hz' : z ∈ p'.support)
    (hord : p.support.idxOf v < p.support.idxOf z)
    (hord' : p'.support.idxOf v < p'.support.idxOf z) :
    predecessor p z = predecessor p' z := by
  have hne : v ≠ z := by intro h; subst z; omega
  have hmem : v ∈ (p.takeUntil z hz).support := by
    apply ((p.support_takeUntil_prefix_support hz).mem_iff_idxOf_lt_length v).mpr
    rw [Walk.length_support, Walk.length_takeUntil]
    omega
  have hmem' : v ∈ (p'.takeUntil z hz').support := by
    apply ((p'.support_takeUntil_prefix_support hz').mem_iff_idxOf_lt_length v).mpr
    rw [Walk.length_support, Walk.length_takeUntil]
    omega
  let q := (p.takeUntil z hz).dropUntil v hmem
  let q' := (p'.takeUntil z hz').dropUntil v hmem'
  have hq : q.IsSubwalk p := (Walk.isSubwalk_dropUntil _ _).trans (p.isSubwalk_takeUntil hz)
  have hq' : q'.IsSubwalk p' := (Walk.isSubwalk_dropUntil _ _).trans (p'.isSubwalk_takeUntil hz')
  have heq : q = q' := optimal_subpaths_eq hp hp' hq hq'
  rw [predecessor_subwalk_end hp.2.1 hq hne, predecessor_subwalk_end hp'.2.1 hq' hne, heq]

noncomputable def routing {G : V → V → Prop} {w : V → V → ℝ≥0}
    (s t : I → V) (p : ∀ i, K.Walk (s i) (t i)) (hp : ∀ i, Optimal G w (p i)) :
    Routing I V where
  pred i := predecessor (p i)
  rank i v := (p i).support.idxOf v
  rank_inj i v z hv hz heq := (List.idxOf_inj (predecessor_mem hv)).mp heq
  consistent i j v z hiv hjv hiz hjz hi hj := consistent_predecessors
    (hp i) (hp j) (predecessor_mem hiv) (predecessor_mem hiz)
    (predecessor_mem hjv) (predecessor_mem hjz) hi hj

end LinearDistancePreservers.ConsistentTiebreaking
