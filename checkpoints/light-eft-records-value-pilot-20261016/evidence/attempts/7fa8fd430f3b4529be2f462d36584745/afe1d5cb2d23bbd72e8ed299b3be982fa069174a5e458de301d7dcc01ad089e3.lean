import LightEFTSpanners.SampledHostExpectation
import LightEFTSpanners.InducedExtremalHost


namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners
variable {V W J : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] [DecidableEq W] in
private theorem blocking_seed_enumeration {G Q : SimpleGraph W} {w : Sym2 W → ℝ}
    {t : ℝ} {f : ℕ} {B : Sym2 W → Finset (Sym2 W)} (a : Fintype Q.edgeSet)
    (hB : BlockingData G (@SimpleGraph.edgeFinset W Q a) w t f B) :
    BlockingData G (@SimpleGraph.edgeFinset W Q
      (@SimpleGraph.fintypeEdgeSet W Q inferInstance (fun _ _ => Classical.propDecidable _))) w t f B := by
  cases Subsingleton.elim a (@SimpleGraph.fintypeEdgeSet W Q inferInstance
    (fun _ _ => Classical.propDecidable _))
  exact hB

/-- Every sampled host's actually retained greedy graph admits the existing
local girth/pruning/extremal bound on its own genuine vertex domain. -/
theorem retained_host_extremal_bound (j : V ↪ W) (T : SimpleGraph V) (hT : T.IsTree)
    (w : Sym2 W → ℝ) (eps : ℝ) (k : ℕ) (hk : 0<k) (heps : 0<eps)
    (a : J) (S : Finset (Sym2 W)) (rs : List (Sym2 W × Finset J))
    (hs : (rs.map Prod.fst).Pairwise (fun e d => w d≤w e))
    (hn : (rs.map Prod.fst).Nodup)
    (hdis : ∀ e∈rs.map Prod.fst,e∉(T.map j).edgeFinset)
    (hdiag : ∀ e∈rs.map Prod.fst,¬e.IsDiag)
    (himage : ∀ e A,(e,A)∈rs → a∈A → ∃ d,j.sym2Map d=e)
    (hw : ∀ e∈(T.map j).edgeFinset∪(rs.map Prod.fst).toFinset,0<w e) :
    retainedWeight (T.map j).edgeFinset w ((1+eps)*(2*k-1)) a S rs≤
      4*extremalLightness (Fintype.card W) ((1+eps)*(2*k-1)+1)*totalWeight (T.map j) w := by
  classical
  let t : ℝ := (1+eps)*(2*k-1)
  let l := selectedList a S rs
  let E := greedyEdges (T.map j).edgeFinset w t 0 l
  let C := edgeGraph E
  let U := E\(T.map j).edgeFinset
  have hls := selectedList_sublist a S rs
  have hnd : ∀ e∈(T.map j).edgeFinset∪l.toFinset,¬e.IsDiag := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact (T.map j).not_isDiag_of_mem_edgeFinset he
    · exact hdiag e (hls.subset (List.mem_toFinset.mp he))
  have ht : 0≤t+1 := by have hh := actual_threshold_gt_two heps hk;dsimp [t];linarith
  obtain ⟨B,hB⟩ := greedy_has_blocking (T.map j).edgeFinset w t 0 ht l
    (hs.sublist hls) (hls.nodup hn) (fun e he => hdis e (hls.subset he)) hnd
  have hBC (e) : B e=∅ := card_eq_zero.mp (Nat.le_zero.mp (hB.capped e))
  have hTC : T.map j≤C := by
    have hh := edgeGraph_mono (greedy_seed_subset (T.map j).edgeFinset w t 0 l)
    simpa only [edgeGraph,coe_edgeFinset,fromEdgeSet_edgeSet,C,E] using hh
  have hUC : ∀ e∈U,e∈C.edgeSet := by
    intro e he
    have heE := (mem_sdiff.mp he).1
    exact (mem_edgeGraph E e).mpr ⟨heE,hnd e (greedy_subset _ _ _ _ _ heE)⟩
  have hUmap : (pullEdges j U).map j.sym2Map=U := by
    ext e
    constructor
    · rintro he
      obtain ⟨d,hd,rfl⟩ := mem_map.mp he
      exact (mem_pullEdges j U d).mp hd
    · intro he
      obtain ⟨heE,heT⟩ := mem_sdiff.mp he
      have hel := List.mem_toFinset.mp ((mem_union.mp (greedy_subset _ _ _ _ _ heE)).resolve_left heT)
      obtain ⟨A,hA,ha⟩ := selectedList_record a S rs hel
      obtain ⟨d,rfl⟩ := himage e A hA ha
      exact mem_map.mpr ⟨d,(mem_pullEdges j U d).mpr he,rfl⟩
  have hwC : ∀ e∈C.edgeSet,0<w e := by
    intro e he
    rcases mem_union.mp (greedy_subset _ _ _ _ _ ((mem_edgeGraph E e).mp he).1) with he | he
    · exact hw e (mem_union_left _ he)
    · exact hw e (mem_union_right _ (List.mem_toFinset.mpr (hls.subset (List.mem_toFinset.mp he))))
  have hp := induced_host_extremal_global_order (f:=0) (r:=1) (G:=C) (Q:=T.map j) (T:=T) (w:=w) (eps:=eps) (k:=k) j hTC
    (blocking_seed_enumeration _ hB) hT (le_refl (T.map j))
    (pullEdges j U) (fun e he => hUC _ ((mem_pullEdges j U e).mp he))
    (fun e he => by simpa only [mem_edgeFinset] using (mem_sdiff.mp ((mem_pullEdges j U e).mp he)).2)
    (fun e _ => by simp [hBC]) (fun e _ => by simp [hBC]) hwC (by decide) hk heps
  simpa only [hUmap,Nat.cast_one,mul_one,retainedWeight,U,E,l,t] using hp
end LightEFTSpanners.SampledGreedy
