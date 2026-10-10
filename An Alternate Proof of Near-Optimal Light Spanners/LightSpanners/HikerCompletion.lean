import LightSpanners.HikerLayers

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

theorem bucketWalk_copy {u v u' v' : V} {i s : ℕ} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (hp : C.BucketWalk i s p) :
    C.BucketWalk i s (p.copy hu hv) := by
  subst_vars
  exact hp

theorem backwardWalk_cycleDarts (t : ℕ) (v : V) :
    C.cycleDarts (C.backwardWalk t v) = (C.backwardWalk t v).darts := by
  apply List.filter_eq_self.mpr
  intro d hd
  have hm : d.edge ∈ C.cycle.edges := by
    rw [← d.edge_symm]
    exact List.mem_map.mpr ⟨d.symm,C.backwardWalk_darts t v d hd,rfl⟩
  simpa using hm

theorem backwardWalk_chordEdges (t : ℕ) (v : V) :
    C.chordEdges (C.backwardWalk t v) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
  have hm : d.edge ∈ C.cycle.edges := by
    rw [← d.edge_symm]
    exact List.mem_map.mpr ⟨d.symm,C.backwardWalk_darts t v d hd,rfl⟩
  simpa using hm

theorem backwardWalk_nonbacktracking (t : ℕ) (v : V) :
    (C.backwardWalk t v).edges.IsChain (· ≠ ·) := by
  apply (List.isChain_map Dart.edge).mpr
  apply (C.backwardWalk t v).isChain_dartAdj_darts.imp_of_mem_imp
  intro d e hd he hadj
  have hn := WalkSquad.forward_darts_ne C (C.backwardWalk_darts t v e he)
    (C.backwardWalk_darts t v d hd) (show G.DartAdj e.symm d.symm from hadj.symm)
  simpa using hn.symm

theorem concat_chord_append_backward_nonbacktracking {u v z : V}
    (p : G.Walk u v) (h : G.Adj v z) (t : ℕ)
    (hp : (p.concat h).edges.IsChain (· ≠ ·)) (hc : s(v,z) ∉ C.cycle.edges) :
    ((p.concat h).append (C.backwardWalk t z)).edges.IsChain (· ≠ ·) := by
  rw [Walk.edges_append]
  apply List.IsChain.append hp (C.backwardWalk_nonbacktracking t z)
  intro e he f hf hef
  have heq : e = s(v,z) := by simpa [Walk.edges_concat,List.concat_eq_append,eq_comm] using he
  have hfm : f ∈ (C.backwardWalk t z).edges := List.mem_of_mem_head? hf
  obtain ⟨d,hd,hdf⟩ := List.mem_map.mp hfm
  have hm : d.edge ∈ C.cycle.edges := by
    rw [← d.edge_symm]
    exact List.mem_map.mpr ⟨d.symm,C.backwardWalk_darts t z d hd,rfl⟩
  exact hc (by simpa [hdf,← hef,heq] using hm)

/-- Cancel precisely the terminal forward-cycle suffix, then complete by
backward cycle steps. Actual endpoints and every chord are preserved. -/
theorem exists_balanced_completion {u v : V} (p : G.Walk u v) (i : ℕ)
    (hnb : p.edges.IsChain (· ≠ ·))
    (hforward : ∀ d ∈ C.cycleDarts p, d ∈ C.cycle.darts)
    (hweights : ∀ e ∈ C.chordEdges p, (2:ℝ)^i ≤ w e ∧ w e < 2^(i+1)) :
    ∃ (s : ℕ) (q : G.Walk u ((C.successor.symm : V → V)^[(C.cycleDarts p).length] v)),
      s ≤ (C.cycleDarts p).length ∧ C.BucketWalk i s q ∧ C.chordEdges q = C.chordEdges p := by
  induction p using Walk.concatRec with
  | Hnil => exact ⟨0,.nil,le_rfl,C.bucketWalk_nil i _,rfl⟩
  | @Hconcat u v z p h ih =>
    have hpnb : p.edges.IsChain (· ≠ ·) := by
      rw [Walk.edges_concat,List.concat_eq_append] at hnb
      exact hnb.left_of_append
    have hpf : ∀ d ∈ C.cycleDarts p, d ∈ C.cycle.darts := by
      intro d hd
      apply hforward d
      rw [Walk.concat_eq_append,C.cycleDarts_append]
      exact List.mem_append_left _ hd
    have hpw : ∀ e ∈ C.chordEdges p, (2:ℝ)^i ≤ w e ∧ w e < 2^(i+1) := by
      intro e he
      apply hweights e
      rw [Walk.concat_eq_append,C.chordEdges_append]
      exact List.mem_append_left _ he
    by_cases hc : s(v,z) ∈ C.cycle.edges
    · have hlen : (C.cycleDarts (p.concat h)).length = (C.cycleDarts p).length+1 := by
        rw [Walk.concat_eq_append,C.cycleDarts_append]
        simp [cycleDarts,hc]
      have hlast : (⟨(v,z),h⟩ : G.Dart) ∈ C.cycle.darts := by
        apply hforward
        simp [cycleDarts,Walk.darts_concat,List.concat_eq_append,hc]
      have hs : C.successor.symm z = v := by
        have he := (C.dart_mem_iff_successor _).mp hlast
        exact C.successor.symm_apply_eq.mpr he.symm
      have hend : (C.successor.symm : V → V)^[(C.cycleDarts (p.concat h)).length] z =
          (C.successor.symm : V → V)^[(C.cycleDarts p).length] v := by
        rw [hlen,Function.iterate_succ_apply,hs]
      obtain ⟨s,q,hsbound,hq,hch⟩ := ih hpnb hpf hpw
      refine ⟨s,q.copy rfl hend.symm,by omega,?_,?_⟩
      · exact C.bucketWalk_copy q rfl hend.symm hq
      · simpa [chordEdges,Walk.edges_concat,List.concat_eq_append,hc] using hch
    · let t := (C.cycleDarts (p.concat h)).length
      let q := (p.concat h).append (C.backwardWalk t z)
      have hch : C.chordEdges q = C.chordEdges (p.concat h) := by
        dsimp only [q]
        rw [C.chordEdges_append,C.backwardWalk_chordEdges,List.append_nil]
      refine ⟨t,q,le_rfl,?_,hch⟩
      refine ⟨C.concat_chord_append_backward_nonbacktracking p h t hnb hc,?_,
        C.cycleDarts (p.concat h),(C.backwardWalk t z).darts,?_,rfl,?_,hforward,?_⟩
      · simpa only [hch] using hweights
      · dsimp only [q]
        rw [C.cycleDarts_append,C.backwardWalk_cycleDarts]
      · simp
      · exact C.backwardWalk_darts t z

end LightSpanners.UnitSpanningCycle
