import LightSpanners.CycleBalance

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Split an actual walk at the first dart in its oriented chord word. -/
theorem exists_first_chord_split {u v : V} (p : G.Walk u v)
    {d : G.Dart} {ds : List G.Dart} (he : C.chordDarts p = d :: ds) :
    ∃ (a : G.Walk u d.fst) (b : G.Walk d.snd v),
      p = a.append (.cons d.adj b) ∧ C.chordDarts a = [] ∧ C.chordDarts b = ds := by
  induction p with
  | nil => simp at he
  | @cons u z v h p ih =>
    by_cases hc : s(u,z) ∈ C.cycle.edges
    · have ht : C.chordDarts p = d :: ds := by
        simpa [chordDarts,Walk.darts_cons,hc] using he
      obtain ⟨a,b,hp,ha,hb⟩ := ih ht
      refine ⟨.cons h a,b,?_,?_,hb⟩
      · simp [hp]
      · simpa [chordDarts,Walk.darts_cons,hc] using ha
    · have ht : (⟨(u,z),h⟩ : G.Dart) :: C.chordDarts p = d :: ds := by
        simpa [chordDarts,Walk.darts_cons,hc] using he
      obtain ⟨hd,hds⟩ := List.cons.inj ht
      subst d
      exact ⟨.nil,p,rfl,rfl,hds⟩

theorem edges_base_of_chordDarts_nil {u v : V} (p : G.Walk u v)
    (h : C.chordDarts p = []) : ∀ e ∈ p.edges, e ∈ C.cycle.edges := by
  have he : C.chordEdges p = [] := by rw [← C.chordDarts_map_edges p,h]; rfl
  intro e hp
  by_contra hn
  have : e ∈ C.chordEdges p := by simp [chordEdges,hp,hn]
  simp [he] at this

theorem length_eq_cycleDarts_of_chordDarts_nil {u v : V} (p : G.Walk u v)
    (h : C.chordDarts p = []) : p.length = (C.cycleDarts p).length := by
  have he : C.chordEdges p = [] := by rw [← C.chordDarts_map_edges p,h]; rfl
  simpa [he] using C.length_split p

variable [Fintype V]

/-- A non-backtracking base walk shorter than the spanning cycle is a path. -/
theorem base_walk_isPath {u v : V} (p : G.Walk u v)
    (hnb : p.edges.IsChain (· ≠ ·))
    (hbase : ∀ e ∈ p.edges, e ∈ C.cycle.edges)
    (hlen : p.length < Fintype.card V) : p.IsPath := by
  apply isPath_of_no_supported_cycle p hnb
  intro z q hq hqp
  have hc := C.base_cycle_length_le_cycleDarts p q hq hqp (fun e he => hbase e (hqp he))
  have hb : (C.cycleDarts p).length ≤ p.length := by
    exact (List.length_filter_le _ _).trans_eq p.length_darts
  omega

/-- A short collection of base arcs is uniquely determined by its endpoints
and the intervening oriented chord word. -/
theorem walks_eq_of_chordDarts {u v : V} (p q : G.Walk u v)
    (hp : p.edges.IsChain (· ≠ ·)) (hq : q.edges.IsChain (· ≠ ·)) (he : C.chordDarts p = C.chordDarts q)
    (hlen : (C.cycleDarts p).length + (C.cycleDarts q).length < Fintype.card V) : p = q := by
  generalize hn : (C.chordDarts p).length = n
  induction n generalizing u v with
  | zero =>
    have hpn : C.chordDarts p = [] := List.length_eq_zero_iff.mp hn
    have hqn : C.chordDarts q = [] := he.symm.trans hpn
    have hsize : p.length + q.length < Fintype.card V := by
      simpa only [C.length_eq_cycleDarts_of_chordDarts_nil p hpn,
        C.length_eq_cycleDarts_of_chordDarts_nil q hqn] using hlen
    exact C.short_base_paths_unique p q
      (C.base_walk_isPath p hp (C.edges_base_of_chordDarts_nil p hpn) (by omega))
      (C.base_walk_isPath q hq (C.edges_base_of_chordDarts_nil q hqn) (by omega))
      (C.edges_base_of_chordDarts_nil p hpn) (C.edges_base_of_chordDarts_nil q hqn) hsize
  | succ n ih =>
    obtain ⟨d,ds,hword⟩ : ∃ d ds, C.chordDarts p = d :: ds := by
      cases hw : C.chordDarts p with
      | nil => simp [hw] at hn
      | cons d ds => exact ⟨d,ds,rfl⟩
    obtain ⟨a,b,hpab,ha,hb⟩ := C.exists_first_chord_split p hword
    obtain ⟨a',b',hqab,ha',hb'⟩ := C.exists_first_chord_split q (he.symm.trans hword)
    have hp' := hp
    have hq' := hq
    rw [hpab,Walk.edges_append,Walk.edges_cons] at hp'
    rw [hqab,Walk.edges_append,Walk.edges_cons] at hq'
    have hsize : a.length + a'.length < Fintype.card V := by
      rw [C.length_eq_cycleDarts_of_chordDarts_nil a ha,
        C.length_eq_cycleDarts_of_chordDarts_nil a' ha']
      rw [hpab,hqab,C.cycleDarts_append,C.cycleDarts_append,List.length_append,List.length_append] at hlen
      omega
    have heqa : a = a' := C.short_base_paths_unique a a'
      (C.base_walk_isPath a hp'.left_of_append (C.edges_base_of_chordDarts_nil a ha) (by omega))
      (C.base_walk_isPath a' hq'.left_of_append (C.edges_base_of_chordDarts_nil a' ha') (by omega))
      (C.edges_base_of_chordDarts_nil a ha) (C.edges_base_of_chordDarts_nil a' ha') hsize
    have hd : d.edge ∉ C.cycle.edges := by
      have hm : d ∈ C.chordDarts p := by rw [hword]; simp
      simpa [chordDarts] using (List.mem_filter.mp hm).2
    have hsize' : (C.cycleDarts b).length + (C.cycleDarts b').length < Fintype.card V := by
      rw [hpab,hqab,C.cycleDarts_append,C.cycleDarts_append,List.length_append,List.length_append] at hlen
      have hcb : C.cycleDarts (.cons d.adj b) = C.cycleDarts b := by
        change List.filter (fun e : G.Dart => decide (e.edge ∈ C.cycle.edges)) (d :: b.darts) = _
        simp [hd,cycleDarts]
      have hcb' : C.cycleDarts (.cons d.adj b') = C.cycleDarts b' := by
        change List.filter (fun e : G.Dart => decide (e.edge ∈ C.cycle.edges)) (d :: b'.darts) = _
        simp [hd,cycleDarts]
      rw [hcb,hcb'] at hlen
      omega
    have hn' : (C.chordDarts b).length = n := by rw [hb]; rw [hword,List.length_cons] at hn; omega
    have heqb : b = b' := ih b b' hp'.right_of_append.tail hq'.right_of_append.tail
      (hb.trans hb'.symm) hsize' hn'
    rw [hpab,hqab,heqa,heqb]

end LightSpanners.UnitSpanningCycle
