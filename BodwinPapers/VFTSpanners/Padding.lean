import BodwinPapers.VFTSpanners.Extremal

set_option backward.isDefEq.respectTransparency.types false

namespace BodwinPapers.VFTSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

abbrev mapHom {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) : G →g G.map f where
  toFun := f
  map_rel' := fun h => SimpleGraph.map_adj_apply' h (f.injective.ne h.ne)

/-- Walks in an injectively relabeled graph lift to the original graph. -/
theorem lift_map_walk {V W : Type*} (G : SimpleGraph V) (f : V ↪ W)
    {a b : W} (p : (G.map f).Walk a b) :
    ∀ (u : V) (hu : f u = a), ∃ (v : V) (hv : f v = b), ∃ q : G.Walk u v,
      (q.map (mapHom G f)).copy hu hv = p := by
  induction p with
  | nil =>
    intro u hu
    exact ⟨u,hu,.nil,by subst hu; rfl⟩
  | @cons a z b haz p ih =>
    intro u hu
    obtain ⟨_,x,y,hxy,hx,hy⟩ := haz
    have hux : u = x := f.injective (hu.trans hx.symm)
    subst x
    subst a
    subst z
    obtain ⟨v,hv,q,hq⟩ := ih y rfl
    subst b
    simp only [Walk.copy_rfl_rfl] at hq
    subst p
    exact ⟨v,rfl,.cons hxy q,rfl⟩

/-- Adding isolated vertices cannot introduce any cycle. -/
theorem HighGirth.map {V W : Type*} {G : SimpleGraph V} {k : ℕ}
    (hg : HighGirth G k) (f : V ↪ W) : HighGirth (G.map f) k := by
  intro a p hp
  have ha : ∃ u, f u = a := by
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h p => exact ⟨h.2.choose, h.2.choose_spec.choose_spec.2.1⟩
  obtain ⟨u,rfl⟩ := ha
  obtain ⟨v,hv,q,hq⟩ := lift_map_walk G f p u rfl
  have hvu : v = u := f.injective hv
  subst v
  simp only [Walk.copy_rfl_rfl] at hq
  have hqc : q.IsCycle := Walk.IsCycle.of_map (hq.symm ▸ hp)
  have hlen := congrArg Walk.length hq
  have hlen' : q.length = p.length := by simpa using hlen
  exact hlen' ▸ hg u q hqc

/-- Monotonicity of the paper's extremal function in the number of vertices. -/
theorem extremalEdges_mono {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    extremalEdges m k ≤ extremalEdges n k := by
  classical
  change ((univ : Finset (SimpleGraph (Fin m))).filter (fun G => HighGirth G k)).sup
    (fun G => G.edgeFinset.card) ≤ extremalEdges n k
  apply Finset.sup_le
  intro G hG
  have hg := (mem_filter.mp hG).2
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have h := edge_count_le_extremal (G.map f) n k (by simp) (hg.map f)
  convert h using 1
  convert (card_edgeFinset_map f G).symm using 2; ext e; simp [G.edgeSet_map f]

/-- Rounded form of Theorem 1 with the paper's `n/f` scale. -/
theorem blocking_extremal_bound_paper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset (V × Sym2 V)) (k f : ℕ)
    (hf : 1 ≤ f) (hB : IsBlockingSet G k (B : Set (V × Sym2 V)))
    (hb : B.card ≤ f*G.edgeFinset.card) :
    G.edgeFinset.card ≤ 36*f^2 * extremalEdges (max 2 (Fintype.card V / f)) k := by
  classical
  have h := blocking_extremal_bound G B k f hf hB hb
  apply h.trans
  apply Nat.mul_le_mul_left
  apply extremalEdges_mono
  exact max_le_max_left _ (Nat.div_le_div_left (by omega : f ≤ 2*f) (by omega))

end BodwinPapers.VFTSpanners
