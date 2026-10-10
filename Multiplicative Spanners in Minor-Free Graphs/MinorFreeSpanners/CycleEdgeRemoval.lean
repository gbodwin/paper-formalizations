import MinorFreeSpanners.Greedy

namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Remove a chosen edge from an actual closed trail, reconnecting the
remaining prefix and suffix into an endpoint-to-endpoint walk. -/
theorem closed_trail_remove_edge {a : V} (p : G.Walk a a) (hp : p.IsTrail)
    (e : Sym2 V) (he : e ∈ p.edges) :
    ∃ (u v : V) (_huv : G.Adj u v), s(u,v) = e ∧
      ∃ q : G.Walk v u, e ∉ q.edges ∧ q.length+1 = p.length ∧
        ∀ f ∈ q.edges, f ∈ p.edges := by
  classical
  obtain ⟨d,hd,hde⟩ := List.mem_map.mp he
  obtain ⟨l,r,hlr⟩ := (Walk.isSubwalk_toWalk_adj_iff_mem_darts p).mpr hd
  have hnodup : (l.edges ++ s(d.fst,d.snd) :: r.edges).Nodup := by
    simpa [hlr,Adj.toWalk,Walk.edges_append,List.append_assoc] using hp.edges_nodup
  refine ⟨d.fst,d.snd,d.adj,hde,r.append l,?_,?_,?_⟩
  · simp only [Walk.edges_append,List.mem_append,not_or]
    rw [← hde]
    change s(d.fst,d.snd) ∉ r.edges ∧ s(d.fst,d.snd) ∉ l.edges
    simp only [List.nodup_append,List.nodup_cons] at hnodup
    grind
  · simp only [hlr,Walk.length_append,Adj.toWalk,Walk.length_cons,Walk.length_nil]
    omega
  · intro f hf
    simp only [Walk.edges_append,List.mem_append] at hf
    simp only [hlr,Walk.edges_append,Adj.toWalk,Walk.edges_cons,Walk.edges_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto

end MinorFreeSpanners
