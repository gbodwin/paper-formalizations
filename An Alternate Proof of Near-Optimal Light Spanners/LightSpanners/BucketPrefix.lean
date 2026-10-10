import LightSpanners.HikerCompletion

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

omit [DecidableEq V] in
theorem balanced_list_prefix {α : Type*} (a c f b : List α)
    (h : a++c=f++b) (hlen : f.length=b.length) :
    ∃ f' b', a=f'++b' ∧ List.IsPrefix f' f ∧ List.IsPrefix b' b ∧
      b'.length ≤ f'.length ∧ f'.length ≤ f.length := by
  rcases List.append_eq_append_iff.mp h with ⟨t,hf,_⟩ | ⟨t,ha,hb⟩
  · refine ⟨a,[],by simp,⟨t,hf.symm⟩,by simp,by simp,?_⟩
    rw [hf,List.length_append]
    omega
  · refine ⟨f,t,ha,List.prefix_refl _,⟨c,hb.symm⟩,?_,le_rfl⟩
    rw [hb,List.length_append] at hlen
    omega

/-- A prefix ending immediately after a chord can be completed by backward
cycle steps into a balanced bucket walk without changing any of its chords.
The new forward budget never exceeds the original one. -/
theorem BucketWalk.complete_chord_prefix {u x y v : V} {i s : ℕ}
    (p : G.Walk u x) (h : G.Adj x y) (r : G.Walk y v)
    (hp : C.BucketWalk i s ((p.concat h).append r)) (hc : s(x,y) ∉ C.cycle.edges) :
    ∃ (s' : ℕ) (z : V) (q : G.Walk u z), s' ≤ s ∧ C.BucketWalk i s' q ∧
      C.chordEdges q=C.chordEdges (p.concat h) := by
  obtain ⟨hnb,hw,f,b,he,hf,hb,hfor,hback⟩ := hp
  rw [C.cycleDarts_append] at he
  obtain ⟨f',b',hprefix,hff,hbb,hbf,hf'⟩ :=
    balanced_list_prefix (C.cycleDarts (p.concat h)) (C.cycleDarts r) f b he (hf.trans hb.symm)
  let t := f'.length-b'.length
  let q := (p.concat h).append (C.backwardWalk t y)
  have hpnb : (p.concat h).edges.IsChain (· ≠ ·) := by
    rw [Walk.edges_append] at hnb
    exact hnb.left_of_append
  have hch : C.chordEdges q=C.chordEdges (p.concat h) := by
    dsimp only [q]
    rw [C.chordEdges_append,C.backwardWalk_chordEdges,List.append_nil]
  refine ⟨f'.length,_,q,hf'.trans_eq hf,?_,hch⟩
  refine ⟨C.concat_chord_append_backward_nonbacktracking p h t hpnb hc,?_,
    f',b'++(C.backwardWalk t y).darts,?_,rfl,?_,?_,?_⟩
  · intro e he
    apply hw e
    rw [hch] at he
    rw [C.chordEdges_append]
    exact List.mem_append_left _ he
  · dsimp only [q]
    rw [C.cycleDarts_append,C.backwardWalk_cycleDarts,hprefix,List.append_assoc]
  · simp only [List.length_append,Walk.length_darts,backwardWalk_length]
    dsimp only [t]
    omega
  · exact fun d hd => hfor d (hff.sublist.subset hd)
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hback d (hbb.sublist.subset hd)
    · exact C.backwardWalk_darts t y d hd

end LightSpanners.UnitSpanningCycle
