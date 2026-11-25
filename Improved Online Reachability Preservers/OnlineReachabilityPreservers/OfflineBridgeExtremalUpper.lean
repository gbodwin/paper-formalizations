import OnlineReachabilityPreservers.OfflineIndependence
import OnlineReachabilityPreservers.LocalOrderExtremal

/-! The upper direction of Lemma 14 measured directly against the unrestricted bridge-free maximum. -/

namespace OnlineReachabilityPreservers

open Finset

universe u

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem Bridge.pathCount_le {V I : Type*} [Fintype I] {before : I → V → V → Prop}
    {k : ℕ} (b : Bridge before k) : k+2 ≤ Fintype.card I := by
  classical
  let used := (univ : Finset (Fin (k+1))).map ⟨b.arc,b.distinctArcs⟩
  have no : b.river ∉ used := by
    intro present
    obtain ⟨i,_,eq⟩ := mem_map.mp present
    exact b.river_ne_arc i eq.symm
  have count : used.card = k+1 := by simp [used]
  have bound := card_le_univ (insert b.river used)
  rw [card_insert_of_notMem no, count] at bound
  exact bound

private theorem relabel_ordered_sets {W V I J : Type*} [LinearOrder W] [DecidableEq V] [Fintype I] [Fintype J]
    (paths : I → Finset W) (vertices : W ≃ V) (indices : J ≃ I)
    (free : ∀ size, BridgeFree (PathBefore paths) size) :
    ∃ rows : J → List V, (∀ i, (rows i).Nodup) ∧
      (∑ i, (rows i).length) = ∑ i, (paths i).card ∧
      ∀ size, BridgeFree (ListBefore rows) size := by
  let rows (j : J) := ((paths (indices j)).sort).map vertices
  have restored (j : J) : (rows j).map vertices.symm = (paths (indices j)).sort := by
    simp [rows, List.map_map, Function.comp_def]
  refine ⟨rows, fun j => (sort_nodup _ _).map vertices.injective, ?_, ?_⟩
  · simp only [rows, List.length_map, length_sort]
    exact Equiv.sum_comp indices (fun i => (paths i).card)
  · intro size k fits
    refine ⟨fun b => ?_⟩
    have step (j : J) (u v : V) (on : ListBefore rows j u v) :
        PathBefore paths (indices j) (vertices.symm u) (vertices.symm v) := by
      have simple : ((rows j).map vertices.symm).Nodup := by rw [restored]; exact sort_nodup _ _
      have mapped := listBefore_map vertices.symm simple on
      have orderedStep : PathBefore (fun i : J => paths (indices i)) j (vertices.symm u) (vertices.symm v) :=
        listBefore_of_sorted_finset (by simpa only [restored] using mapped)
      exact orderedStep
    let relabeled : Bridge (PathBefore (fun j => paths (indices j))) k :=
      b.mapVertices vertices.symm vertices.symm.injective step
    exact (free size fits).false
      (relabeled.mapPaths indices indices.injective (fun _ _ _ h => h))

/-- At positive vertex and demand counts, one maximizer of the fully
bridge-free path-system mass bounds every offline instance at those counts.
The bound includes the exact additive allowance for SCC connectors. -/
theorem theorem14_offline_upper_by_bridge_mass (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧
      (∀ i, paths i ≠ []) ∧
      (∀ size, BridgeFree (ListBefore paths) size) ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) →
        (∀ size, BridgeFree (ListBefore other) size) → (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∀ (V : Type u) [LinearOrder V] [Fintype V] (G : Arcs V) (D : List (V × V)),
        Fintype.card V = n → D.length = p →
        let M := ∑ i, (paths i).length
        let H := offlinePreserver G D
        H ⊆ G ∧ Preserves G H D ∧ H.card+p ≤ M+2*n ∧ H.card ≤ 3*M := by
  obtain ⟨paths,simple,legal,maximal,dense,_⟩ := localOrderExtremal_isDense n p p false hn hp
  refine ⟨paths,simple,localOrderMaximizer_nonempty hn paths legal maximal simple,?_,
    fun other ns free => maximal other ns (free p),?_⟩
  · intro size k _
    exact ⟨fun b => (legal (by simpa only [Fintype.card_fin] using b.pathCount_le)).false b⟩
  · intro V _ _ G D vertexCount demandCount
    let K := condensation G
    let P := D.map (projectDemand G)
    let J := offlinePrune K P
    let ordered := topologicalPaths J (criticalCompressed J P)
    have count : P.length = p := (List.length_map _).trans demandCount
    let indices : Fin p ≃ Fin P.length := finCongr count.symm
    let vertices := (topologicalEquiv J).symm.trans ((Fintype.equivFin V).trans (finCongr vertexCount))
    obtain ⟨_,_,mass,free⟩ := theorem14_dag_compression (condensation_dag G) P
    obtain ⟨rows, noDup, sameMass, noBridges⟩ := relabel_ordered_sets ordered vertices indices free
    have compressMass : (∑ i, (rows i).length) = J.card+p := by rw [sameMass, mass, count]
    have core : J.card+p ≤ ∑ i, (paths i).length := compressMass ▸ maximal rows noDup (noBridges p)
    obtain ⟨sub,correct,overhead⟩ := theorem9_lift offlinePrune G D
      (fun A _ T => (offlinePrune_spec A T).1) (fun A _ T => (offlinePrune_spec A T).2)
    have liftCap : (offlinePreserver G D).card ≤ J.card+2*n := by
      simpa only [vertexCount, offlinePreserver, J, K, P] using overhead
    exact ⟨sub,correct,by omega,by omega⟩

end OnlineReachabilityPreservers
