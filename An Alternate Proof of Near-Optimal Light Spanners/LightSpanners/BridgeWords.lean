import LightSpanners.ChordWords

namespace LightSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- An actual bridge crossed once forces every alternative endpoint walk
through that same edge. The explicit prefix and suffix avoid the bridge. -/
theorem bridge_crossing_forces_edge {u v x y : V}
    (a : G.Walk u x) (b : G.Walk y v) (q : G.Walk u v)
    (hb : G.IsBridge s(x,y)) (ha : s(x,y) ∉ a.edges) (hb' : s(x,y) ∉ b.edges) :
    s(x,y) ∈ q.edges := by
  by_contra hq
  have hh := (isBridge_iff_forall_walk_mem_edges.mp hb) (a.reverse.append (q.append b.reverse))
  simp only [Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse,ha,hb',hq,
    or_self] at hh

omit [DecidableEq V] in
/-- Two bridge-free prefixes from a common start cannot reach opposite
ends of that bridge. This fixes the orientation of a unique bridge crossing. -/
theorem bridge_prefixes_not_opposed {u x y : V}
    (a : G.Walk u x) (b : G.Walk u y)
    (hb : G.IsBridge s(x,y)) (ha : s(x,y) ∉ a.edges) (hb' : s(x,y) ∉ b.edges) : False := by
  have hh := (isBridge_iff_forall_walk_mem_edges.mp hb) (a.reverse.append b)
  simp only [Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse,ha,hb',or_self] at hh

namespace MarkedWalk
variable (S : Set (Sym2 V))
noncomputable def word {u v : V} (p : G.Walk u v) : List G.Dart :=
  p.darts.filter (fun d => d.edge ∈ S)

omit [DecidableEq V] in
@[simp] theorem word_nil (u : V) : word S (.nil : G.Walk u u) = [] := rfl
omit [DecidableEq V] in
@[simp] theorem word_append {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    word S (p.append q) = word S p ++ word S q := by simp [word,Walk.darts_append]

omit [DecidableEq V] in
theorem mem_word {u v : V} (p : G.Walk u v) (d : G.Dart) :
    d ∈ word S p ↔ d ∈ p.darts ∧ d.edge ∈ S := by simp [word]

omit [DecidableEq V] in
theorem word_map_edges {u v : V} (p : G.Walk u v) :
    (word S p).map Dart.edge = p.edges.filter (fun e => e ∈ S) := by
  simp only [word,Walk.edges_eq_map_darts,List.filter_map]
  rfl

omit [DecidableEq V] in
theorem word_nil_iff {u v : V} (p : G.Walk u v) :
    word S p = [] ↔ ∀ e ∈ p.edges, e ∉ S := by
  rw [← List.map_eq_nil_iff (f := Dart.edge),word_map_edges]
  simp

omit [DecidableEq V] in
/-- Split at the first marked dart, retaining actual graph walks. -/
theorem exists_first_split {u v : V} (p : G.Walk u v)
    {d : G.Dart} {ds : List G.Dart} (he : word S p = d :: ds) :
    ∃ (a : G.Walk u d.fst) (b : G.Walk d.snd v),
      p = a.append (.cons d.adj b) ∧ word S a = [] ∧ word S b = ds := by
  induction p with
  | nil => simp at he
  | @cons u z v h p ih =>
    by_cases hc : s(u,z) ∈ S
    · have ht : (⟨(u,z),h⟩ : G.Dart) :: word S p = d :: ds := by
        simpa [word,Walk.darts_cons,hc] using he
      obtain ⟨hd,hds⟩ := List.cons.inj ht
      subst d
      exact ⟨.nil,p,rfl,rfl,hds⟩
    · have ht : word S p = d :: ds := by simpa [word,Walk.darts_cons,hc] using he
      obtain ⟨a,b,hp,ha,hb⟩ := ih ht
      refine ⟨.cons h a,b,?_,?_,hb⟩
      · simp [hp]
      · simpa [word,Walk.darts_cons,hc] using ha

omit [DecidableEq V] in
/-- An edge appearing in a walk has a first crossing with an edge-free prefix. -/
theorem exists_edge_split {u v : V} (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ (d : G.Dart) (a : G.Walk u d.fst) (b : G.Walk d.snd v),
      d.edge = e ∧ p = a.append (.cons d.adj b) ∧ e ∉ a.edges := by
  have hn : word {e} p ≠ [] := by
    intro hh
    exact (word_nil_iff {e} p).mp hh e he (by simp)
  obtain ⟨d,ds,hd⟩ := List.exists_cons_of_ne_nil hn
  obtain ⟨a,b,hp,ha,_⟩ := exists_first_split {e} p hd
  have hm : d ∈ word {e} p := by rw [hd]; simp
  have heq : d.edge = e := by simpa using ((mem_word {e} p d).mp hm).2
  exact ⟨d,a,b,heq,hp,fun hh => (word_nil_iff {e} a).mp ha e hh (by simp)⟩

/-- A marked bridge occurring at most once cannot disappear from any other
walk with the same endpoints. -/
theorem bridge_mem_of_word_nodup {u v : V} (p q : G.Walk u v) {e : Sym2 V}
    (hN : ((word S p).map Dart.edge).Nodup) (he : e ∈ p.edges) (heS : e ∈ S)
    (hB : G.IsBridge e) : e ∈ q.edges := by
  obtain ⟨d,a,b,hde,hp,ha⟩ := exists_edge_split p he
  subst e
  have hN' := hN
  rw [word_map_edges,hp,Walk.edges_append,Walk.edges_cons,List.filter_append] at hN'
  change (a.edges.filter (fun e => e ∈ S) ++
    (d.edge :: b.edges).filter (fun e => e ∈ S)).Nodup at hN'
  simp only [List.filter_cons,heS,decide_true,ite_true] at hN'
  have hnb := (List.nodup_cons.mp (List.nodup_append.mp hN').2.1).1
  have hb : d.edge ∉ b.edges := by
    intro hh
    exact hnb (by simp [hh,heS])
  exact bridge_crossing_forces_edge a b q hB ha hb

/-- If all marked edges are bridges, their oriented word is the same in
any two endpoint walks which each use marked edges at most once. -/
theorem bridge_word_unique {u v : V} (p q : G.Walk u v)
    (hp : ((word S p).map Dart.edge).Nodup) (hq : ((word S q).map Dart.edge).Nodup)
    (hB : ∀ e ∈ S, e ∈ G.edgeSet → G.IsBridge e) : word S p = word S q := by
  generalize hn : (word S p).length = n
  induction n generalizing u v with
  | zero =>
    have hpn : word S p = [] := List.length_eq_zero_iff.mp hn
    have hqn : word S q = [] := by
      apply (word_nil_iff S q).mpr
      intro e he heS
      have hem := bridge_mem_of_word_nodup S q p hq he heS (hB e heS (q.edges_subset_edgeSet he))
      exact (word_nil_iff S p).mp hpn e hem heS
    rw [hpn,hqn]
  | succ n ih =>
    obtain ⟨d,ds,hword⟩ := List.exists_cons_of_length_pos (by omega : 0 < (word S p).length)
    obtain ⟨a,b,hpab,ha,hb⟩ := exists_first_split S p hword
    have hdmem : d ∈ word S p := by rw [hword]; simp
    have hdS := ((mem_word S p d).mp hdmem).2
    have hdpe : d.edge ∈ p.edges := List.mem_map.mpr ⟨d,((mem_word S p d).mp hdmem).1,rfl⟩
    have hdB := hB d.edge hdS (p.edges_subset_edgeSet hdpe)
    have hdqe := bridge_mem_of_word_nodup S p q hp hdpe hdS hdB
    obtain ⟨e,a',b',hed,hqab,ha'e⟩ := exists_edge_split q hdqe
    have had : d.edge ∉ a.edges := fun hh => (word_nil_iff S a).mp ha d.edge hh hdS
    have hed' : e = d := by
      rcases (dart_edge_eq_iff e d).mp hed with hsame | hopp
      · exact hsame
      · subst e
        exact False.elim (bridge_prefixes_not_opposed a a' hdB had ha'e)
    subst e
    have hqparts := hq
    rw [hqab,word_append,List.map_append,List.nodup_append] at hqparts
    have ha' : word S a' = [] := by
      apply (word_nil_iff S a').mpr
      intro e he heS
      have hem := bridge_mem_of_word_nodup S a' a hqparts.1 he heS
        (hB e heS (a'.edges_subset_edgeSet he))
      exact (word_nil_iff S a).mp ha e hem heS
    have hqb : word S (.cons d.adj b') = d :: word S b' := by
      change (d :: b'.darts).filter (fun e => decide (e.edge ∈ S)) = _
      simp [hdS,word]
    have hqword : word S q = d :: word S b' := by rw [hqab,word_append,ha',List.nil_append,hqb]
    have hpbN : ((word S b).map Dart.edge).Nodup := by
      rw [hword,List.map_cons,List.nodup_cons] at hp
      simpa [hb] using hp.2
    have hqbN : ((word S b').map Dart.edge).Nodup := by
      rw [hqword,List.map_cons,List.nodup_cons] at hq
      exact hq.2
    have hn' : (word S b).length = n := by rw [hb]; rw [hword,List.length_cons] at hn; omega
    have heq := ih b b' hpbN hqbN hn'
    rw [hword,hqword,← hb,heq]

/-- Different oriented marked words force an actual cycle containing a
marked edge, provided neither walk repeats a marked edge. -/
theorem exists_marked_cycle {u v : V} (p q : G.Walk u v)
    (hp : ((word S p).map Dart.edge).Nodup) (hq : ((word S q).map Dart.edge).Nodup)
    (hne : word S p ≠ word S q) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ ∃ e ∈ c.edges, e ∈ S := by
  by_contra! hn
  apply hne
  apply bridge_word_unique S p q hp hq
  intro e heS heG
  apply (isBridge_iff_forall_cycle_notMem heG).mpr
  intro z c hc hec
  exact hn z c hc e hec heS

omit [DecidableEq V] in
/-- Inclusion of a support graph preserves the exact oriented marked word. -/
theorem word_mapLe {H : SimpleGraph V} (h : H ≤ G) {u v : V} (p : H.Walk u v) :
    word S (p.mapLe h) = (word S p).map (Hom.ofLE h).mapDart := by
  simp only [word,Walk.darts_map,List.filter_map]
  rfl

/-- Support-local form of marked-cycle extraction. Every resulting cycle edge
lies in one of the two input walks; no global graph cycle is substituted. -/
theorem exists_marked_cycle_in_union {u v : V} (p q : G.Walk u v)
    (hp : ((word S p).map Dart.edge).Nodup) (hq : ((word S q).map Dart.edge).Nodup)
    (hne : word S p ≠ word S q) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧
      (∀ e ∈ c.edges, e ∈ p.edges ∨ e ∈ q.edges) ∧ ∃ e ∈ c.edges, e ∈ S := by
  let H := p.toSubgraph.spanningCoe ⊔ q.toSubgraph.spanningCoe
  have hHG : H ≤ G := sup_le p.toSubgraph.spanningCoe_le q.toSubgraph.spanningCoe_le
  have hH (e : Sym2 V) : e ∈ H.edgeSet ↔ e ∈ p.edges ∨ e ∈ q.edges := by
    simp only [H,edgeSet_sup,Set.mem_union,Subgraph.edgeSet_spanningCoe,Walk.mem_edges_toSubgraph]
  have hpH : ∀ e ∈ p.edges, e ∈ H.edgeSet := fun e he => (hH e).mpr (Or.inl he)
  have hqH : ∀ e ∈ q.edges, e ∈ H.edgeSet := fun e he => (hH e).mpr (Or.inr he)
  have hpmap : (p.transfer H hpH).mapLe hHG = p := by apply Walk.edges_injective; simp
  have hqmap : (q.transfer H hqH).mapLe hHG = q := by apply Walk.edges_injective; simp
  have hpn : ((word S (p.transfer H hpH)).map Dart.edge).Nodup := by
    simpa only [word_map_edges,Walk.edges_transfer] using hp
  have hqn : ((word S (q.transfer H hqH)).map Dart.edge).Nodup := by
    simpa only [word_map_edges,Walk.edges_transfer] using hq
  have hn : word S (p.transfer H hpH) ≠ word S (q.transfer H hqH) := by
    intro he
    apply hne
    have hh := congrArg (List.map (Hom.ofLE hHG).mapDart) he
    simpa only [← word_mapLe,hpmap,hqmap] using hh
  obtain ⟨z,c,hc,e,he,heS⟩ := exists_marked_cycle S _ _ hpn hqn hn
  refine ⟨z,c.mapLe hHG,hc.mapLe hHG,?_,e,?_,heS⟩
  · intro f hf
    have hf' : f ∈ c.edges := by simpa using hf
    exact (hH f).mp (c.edges_subset_edgeSet hf')
  · simpa using he

end MarkedWalk
end LightSpanners
