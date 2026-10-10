import LightSpanners.Distance

namespace LightSpanners
open SimpleGraph
variable {V W : Type*}

/-- Graph homomorphisms preserve walk weight when weights are pulled back. -/
theorem walkWeight_map {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (w : Sym2 W → ℝ) {a b : V} (p : G.Walk a b) :
    walkWeight w (p.map f) = walkWeight (fun e => w (Sym2.map f e)) p := by
  simp [walkWeight, List.map_map, Function.comp_def]

/-- A sublist cannot increase total weight if the ambient list's terms are nonnegative. -/
theorem sublist_weight_le_on {α : Type*} (w : α → ℝ) {l l' : List α}
    (h : l.Sublist l') (hw : ∀ e ∈ l', 0 ≤ w e) :
    (l.map w).sum ≤ (l'.map w).sum := by
  induction h with
  | slnil => simp
  | @cons l l' a h ih =>
    have hi := ih (fun e he => hw e (by simp [he]))
    have ha := hw a (by simp)
    simp only [List.map_cons, List.sum_cons]
    linarith
  | @cons_cons l l' a h ih =>
    have hi := ih (fun e he => hw e (by simp [he]))
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- Loop erasure decreases weight under nonnegativity only on actual graph edges. -/
theorem walkWeight_bypass_le_on_edges [DecidableEq V] {G : SimpleGraph V}
    (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    {a b : V} (p : G.Walk a b) : walkWeight w p.bypass ≤ walkWeight w p :=
  sublist_weight_le_on w p.edges_bypass_sublist_edges
    (fun e he => hw e (p.edges_subset_edgeSet he))

/-- If a chosen cycle edge has a unique projected preimage among that cycle's
edges, projection and loop erasure produce an original cycle containing it.
Thus the original graph's girth inequality bounds the whole lifted cycle. -/
theorem WeightedGirthAbove.cycle_projection_bound [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} {w : Sym2 V → ℝ} {g : ℝ}
    (hG : WeightedGirthAbove G w g) (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (f : H →g G) {a : W} (p : H.Walk a a) (hp : p.IsCycle)
    {e : Sym2 W} (he : e ∈ p.edges)
    (hunique : ∀ d ∈ p.edges, Sym2.map f d = Sym2.map f e → d = e) :
    g * w (Sym2.map f e) < walkWeight (fun d => w (Sym2.map f d)) p := by
  obtain ⟨u, v, rfl, q, hweight, hq⟩ :=
    cycle_complement p hp (fun d => w (Sym2.map f d)) he
  have hadj : H.Adj u v := (mem_edgeSet H).mp (p.edges_subset_edgeSet he)
  have hmap : G.Adj (f u) (f v) := f.map_rel hadj
  let b := (q.map f).bypass
  have hnot : s(f u, f v) ∉ b.edges := by
    intro hd
    have hd' := (q.map f).edges_bypass_sublist_edges.subset hd
    rw [Walk.edges_map, List.mem_map] at hd'
    obtain ⟨d, hdq, heq⟩ := hd'
    exact (hq d hdq).2 (hunique d (hq d hdq).1 (by simpa using heq))
  have hc : (Walk.cons hmap b).IsCycle :=
    (b.cons_isCycle_iff hmap).mpr ⟨(q.map f).bypass_isPath, hnot⟩
  have hg := hG (f u) (.cons hmap b) hc s(f u, f v) (by simp)
  have hb := walkWeight_bypass_le_on_edges w hw (q.map f)
  rw [walkWeight_map] at hb
  simp only [walkWeight_cons] at hg
  simp only [Sym2.map_mk] at hweight ⊢
  change walkWeight w b ≤ _ at hb
  linarith

end LightSpanners
