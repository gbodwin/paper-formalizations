import LightSpanners.WeakCounting

namespace LightSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V} {w : Sym2 V → ℝ}

/-- Weighted-girth lower bounds pass to actual edge subgraphs. -/
theorem WeightedGirthAbove.mono {g : ℝ} (hG : WeightedGirthAbove G w g) (hHG : H≤G) :
    WeightedGirthAbove H w g := by
  intro v p hp e he
  have hh := hG v (p.mapLe hHG) (hp.mapLe hHG) e (by simpa using he)
  simpa using hh

namespace UnitSpanningCycle

noncomputable def liftDart (hHG : H≤G) : H.Dart → G.Dart := (Hom.ofLE hHG).mapDart

@[simp] theorem liftDart_edge (hHG : H≤G) (d : H.Dart) :
    (liftDart hHG d).edge=d.edge := rfl

@[simp] theorem liftDart_symm (hHG : H≤G) (d : H.Dart) :
    liftDart hHG d.symm=(liftDart hHG d).symm := rfl

variable (C : UnitSpanningCycle G w) (D : UnitSpanningCycle H w) (hHG : H≤G)
    (hcycle : D.cycle.darts.map (liftDart hHG)=C.cycle.darts)

include hcycle in
theorem cycle_edges_lift : D.cycle.edges=C.cycle.edges := by
  have hh := congrArg (List.map Dart.edge) hcycle
  simpa [Walk.edges,List.map_map,Function.comp_def] using hh

include hcycle in
theorem chordEdges_mapLe {u v : V} (p : H.Walk u v) :
    C.chordEdges (p.mapLe hHG)=D.chordEdges p := by
  simp [chordEdges,← C.cycle_edges_lift D hHG hcycle]

include hcycle in
theorem cycleDarts_mapLe {u v : V} (p : H.Walk u v) :
    C.cycleDarts (p.mapLe hHG)=(D.cycleDarts p).map (liftDart hHG) := by
  simp [cycleDarts,Walk.mapLe,Walk.darts_map,List.filter_map,
    ← C.cycle_edges_lift D hHG hcycle,liftDart,Function.comp_def,Dart.edge]
  rfl

include hcycle in
theorem BucketWalk.mapLe {u v : V} {i s : ℕ} {p : H.Walk u v}
    (hp : D.BucketWalk i s p) : C.BucketWalk i s (p.mapLe hHG) := by
  obtain ⟨hnb,hw,f,b,he,hf,hb,hfor,hback⟩ := hp
  refine ⟨by simpa using hnb,?_,f.map (liftDart hHG),b.map (liftDart hHG),?_,?_,?_,?_,?_⟩
  · simpa only [C.chordEdges_mapLe D hHG hcycle] using hw
  · rw [C.cycleDarts_mapLe D hHG hcycle,he,List.map_append]
  · simpa using hf
  · simpa using hb
  · intro d hd
    obtain ⟨d',hd',he'⟩ := List.mem_map.mp hd
    subst d
    rw [← hcycle]
    exact List.mem_map.mpr ⟨d',hfor d' hd',rfl⟩
  · intro d hd
    obtain ⟨d',hd',he'⟩ := List.mem_map.mp hd
    subst d
    rw [← liftDart_symm,← hcycle]
    exact List.mem_map.mpr ⟨d'.symm,hback d' hd',rfl⟩

include hcycle in
theorem BucketExtraSafe.mapLe {u v : V} {eps : ℝ} {k i : ℕ} {p : H.Walk u v}
    (hp : D.BucketExtraSafe eps k i p) : C.BucketExtraSafe eps k i (p.mapLe hHG) := by
  obtain ⟨s,hp,hs⟩ := hp
  exact ⟨s,hp.mapLe C D hHG hcycle,hs⟩

include hcycle in
theorem BucketSafe.mapLe {u v : V} {eps : ℝ} {k i : ℕ} {p : H.Walk u v}
    (hp : D.BucketSafe eps k i p) : C.BucketSafe eps k i (p.mapLe hHG) := by
  obtain ⟨s,hp,hs⟩ := hp
  exact ⟨s,hp.mapLe C D hHG hcycle,hs⟩

include hcycle in
theorem BucketMonotoneWalk.mapLe {u v : V} {eps : ℝ} {k J : ℕ} {extra : Bool} {p : H.Walk u v}
    (hp : D.BucketMonotoneWalk eps k extra J p) :
    C.BucketMonotoneWalk eps k extra J (p.mapLe hHG) := by
  induction hp with
  | nil u => exact .nil u
  | snoc hp hq ih =>
    rw [Walk.mapLe_append]
    apply BucketMonotoneWalk.snoc ih
    cases extra
    · exact BucketSafe.mapLe C D hHG hcycle hq
    · exact BucketExtraSafe.mapLe C D hHG hcycle hq

include hcycle in
theorem BucketMonotoneKPath.mapLe {u v : V} {eps : ℝ} {k : ℕ} {extra : Bool} {p : H.Walk u v}
    (hp : D.BucketMonotoneKPath eps k extra p) :
    C.BucketMonotoneKPath eps k extra (p.mapLe hHG) := by
  obtain ⟨hc,J,hp⟩ := hp
  exact ⟨by rwa [C.chordEdges_mapLe D hHG hcycle],J,hp.mapLe C D hHG hcycle⟩

end UnitSpanningCycle
end LightSpanners
