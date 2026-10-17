import LightEFTSpanners.Blocking
import LightSpanners.CycleProjection

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

/-- The actual inverse image of a finite edge set under an injective vertex map. -/
noncomputable def pullEdges (j : V ↪ W) (E : Finset (Sym2 W)) : Finset (Sym2 V) :=
  univ.filter (fun e => j.sym2Map e ∈ E)

omit [DecidableEq V] in
@[simp] theorem mem_pullEdges (j : V ↪ W) (E : Finset (Sym2 W)) (e : Sym2 V) :
    e ∈ pullEdges j E ↔ j.sym2Map e ∈ E := by simp [pullEdges]

omit [DecidableEq V] in
theorem pullEdges_card_le (j : V ↪ W) (E : Finset (Sym2 W)) :
    (pullEdges j E).card ≤ E.card := by
  have hh : (pullEdges j E).map j.sym2Map ⊆ E := by
    intro e he
    obtain ⟨d,hd,rfl⟩ := mem_map.mp he
    exact (mem_pullEdges j E d).mp hd
  simpa only [card_map] using card_le_card hh

omit [Fintype V] [DecidableEq V] [DecidableEq W] in
@[simp] theorem mem_comap_edgeSet (j : V ↪ W) (G : SimpleGraph W) (e : Sym2 V) :
    e ∈ (G.comap j).edgeSet ↔ j.sym2Map e ∈ G.edgeSet := by
  rcases e with ⟨a,b⟩
  rfl

omit [DecidableEq V] in
/-- Blocking data restricts to an actual induced vertex set. A cycle in the
restricted graph maps to a genuine original cycle, so its original blocking
pair also has endpoints in the restricted set. No new blocker oracle is used. -/
theorem BlockingData.comap {G : SimpleGraph W} {seed : Finset (Sym2 W)}
    {w : Sym2 W → ℝ} {t : ℝ} {f : ℕ} {B : Sym2 W → Finset (Sym2 W)}
    (hB : BlockingData G seed w t f B) (j : V ↪ W) :
    BlockingData (G.comap j) (pullEdges j seed) (fun e => w (j.sym2Map e)) t f
      (fun e => pullEdges j (B (j.sym2Map e))) := by
  constructor
  · intro e
    exact (pullEdges_card_le j _).trans (hB.capped _)
  · intro e d hd
    exact (mem_comap_edgeSet j G d).mpr (hB.second_edge _ _ ((mem_pullEdges j _ d).mp hd))
  · intro e d hd
    obtain ⟨he,hs⟩ := hB.first_edge _ _ ((mem_pullEdges j _ d).mp hd)
    exact ⟨(mem_comap_edgeSet j G e).mpr he,fun h => hs ((mem_pullEdges j seed e).mp h)⟩
  · intro e he
    exact hB.no_self _ ((mem_pullEdges j _ e).mp he)
  · intro a p hp d hd hdn hweight
    let J : G.comap j →g G := SimpleGraph.Hom.comap j G
    have hpc : (p.map J).IsCycle := hp.map j.injective
    have hde : j.sym2Map d ∈ (p.map J).edges := by
      rw [Walk.edges_map]
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    have hds : j.sym2Map d ∉ seed := fun h => hdn ((mem_pullEdges j seed d).mpr h)
    have hwp : walkWeight w (p.map J) ≤ (t+1)*w (j.sym2Map d) := by
      rw [walkWeight_map]
      change walkWeight (fun e => w (j.sym2Map e)) p ≤ (t+1)*w (j.sym2Map d)
      exact hweight
    obtain ⟨e,he,b,hb,hbe⟩ := hB.blocks (J a) (p.map J) hpc _ hde hds hwp
    rw [Walk.edges_map] at he hb
    obtain ⟨e',he',rfl⟩ := List.mem_map.mp he
    obtain ⟨b',hb',rfl⟩ := List.mem_map.mp hb
    exact ⟨e',he',b',hb',(mem_pullEdges j _ b').mpr hbe⟩
end LightEFTSpanners
