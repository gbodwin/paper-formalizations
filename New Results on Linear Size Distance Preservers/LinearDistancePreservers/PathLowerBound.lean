import LinearDistancePreservers.PreserverPadding
import LinearDistancePreservers.ModularPerfect
import LinearDistancePreservers.LayeredWalks

/-! The linear lower bound for small terminal sets: an endpoint pair in
an N-vertex path forces all N-1 edges. Additional terminals are harmless. -/
namespace LinearDistancePreservers.PathLowerBound
open SimpleGraph Finset WeightedDigraph WeightedNativeForcing PreserverPadding
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false

theorem realCost_one {V : Type*} {G : SimpleGraph V} {s t : V} (p : G.Walk s t) :
    realCost (fun _ _ => 1) p = (p.length : ℝ) := by
  simp [realCost]

theorem layer_getVert {V : Type*} {G : SimpleGraph V} (l : V → ℤ)
    {s t : V} (p : G.Walk s t)
    (hr : ∀ d ∈ p.darts, l d.snd = l d.fst + 1) :
    ∀ i, i ≤ p.length → l (p.getVert i) = l s + i := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    have hid : i < p.darts.length := by simpa using (show i < p.length by omega)
    have hs := hr p.darts[i] (List.getElem_mem hid)
    simp only [Walk.darts_getElem_eq_getVert] at hs
    have ht := ih (by omega)
    push_cast
    omega

theorem unique_of_layer_injective {V : Type*} {G : SimpleGraph V} (l : V → ℤ)
    (hG : LayeredWalks.Layered G l) (hl : Function.Injective l)
    {s t : V} (p : G.Walk s t) (hp : l t - l s = p.length)
    (q : G.Walk s t) (hq : q.length ≤ p.length) : q = p := by
  have hlo := LayeredWalks.layer_le_length l hG q
  have hlen : q.length = p.length := by omega
  have hq' : l t - l s = (q.length : ℤ) := by omega
  have hpr := LayeredWalks.tight_walk_rises l hG p hp
  have hqr := LayeredWalks.tight_walk_rises l hG q hq'
  apply Walk.ext_getVert_le_length hlen
  intro i hi
  apply hl
  rw [layer_getVert l q hqr i hi,layer_getVert l p hpr i (by omega)]

theorem path_rigid (k : ℕ) :
    Rigid (ModularGraph.graph 1 k 1) (fun _ _ => 1) (ModularGraph.terminals 1 k) := by
  intro H hH hp
  have hlayer : LayeredWalks.Layered (ModularGraph.graph 1 k 1) (fun v => (v.1.val : ℤ)) := by
    rintro u v ⟨b,a,hl,_⟩
    cases b
    · exact Or.inr hl
    · exact Or.inl hl
  have hinj : Function.Injective (fun v : ModularGraph.Vertex 1 k => (v.1.val : ℤ)) := by
    intro u v h
    apply Prod.ext
    · apply Fin.ext
      change (u.1.val : ℤ) = v.1.val at h
      exact_mod_cast h
    · exact Subsingleton.elim _ _
  apply WeightedNativeForcing.eq_of_covers (fun _ _ => 1)
    (fun p : ZMod 1 × Fin 1 => ModularGraph.point p.1 p.2 0)
    (fun p : ZMod 1 × Fin 1 => ModularGraph.point p.1 p.2 (Fin.last k))
    (fun p => ModularGraph.canonicalWalk p.1 p.2)
  · intro p q
    rw [realCost_one,realCost_one,ModularGraph.canonicalWalk_length]
    have hh := LayeredWalks.layer_le_length (fun v => (v.1.val : ℤ)) hlayer q
    have hh' : (k : ℤ) ≤ q.length := by simpa [ModularGraph.point] using hh
    exact_mod_cast hh'
  · intro p q hq
    apply unique_of_layer_injective (fun v => (v.1.val : ℤ)) hlayer hinj
      (ModularGraph.canonicalWalk p.1 p.2)
    · rw [ModularGraph.canonicalWalk_length]
      simp [ModularGraph.point]
    · simp only [realCost_one] at hq
      exact_mod_cast hq.le
  · exact ModularGraph.canonical_covers
  · exact hH
  · intro p
    exact hp _ (ModularGraph.point_start_mem _ _) _ (ModularGraph.point_end_mem _ _)

/-- Exactly N vertices and T terminals, for every 2≤T≤N. -/
theorem exists_path_witness {N T : ℕ} (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (w : Fin N → Fin N → ℝ≥0) (S : Finset (Fin N)),
      S.card = T ∧ Rigid G w S ∧ G.edgeFinset.card = N-1 ∧
      ∀ u v, G.Adj u v → 0 < w u v ∧ w u v = w v u := by
  have hk : 0 < N-1 := by omega
  obtain ⟨G,w,S,hS,hr,hE,hw⟩ := PreserverPadding.pad
    (ModularGraph.graph 1 (N-1) 1) (fun _ _ => 1) (ModularGraph.terminals 1 (N-1))
    (path_rigid (N-1)) (by intros; exact ⟨by norm_num,rfl⟩)
    (N := N) (T := T)
    (by simp [ModularGraph.Vertex,ZMod.card]; omega)
    (by rw [ModularGraph.terminals_card hk]; simpa using hT) hTN
  refine ⟨G,w,S,hS,hr,?_,hw⟩
  rw [hE,ModularGraph.graph_edge_count (by omega : 1 ≤ 1)]
  simp

end LinearDistancePreservers.PathLowerBound
