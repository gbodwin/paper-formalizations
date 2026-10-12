import MinorFreeSpanners.ResidualClusterForest

/-! Extend the chosen initial residual forest before selecting weak cores.
Saturation means every permitted residual edge already has a forest path.
A spanning extension therefore cannot change the residual adjacency. -/
namespace MinorFreeSpanners
open SimpleGraph

 theorem acyclic_adj_of_reachable_subgraph {I : Type*} {H K : SimpleGraph I}
    (hK : K.IsAcyclic) (hHK : H≤K) {i j : I}
    (hij : K.Adj i j) (hreach : H.Reachable i j) : H.Adj i j := by
  obtain ⟨p,hp⟩ := hreach.exists_isPath
  have he := congrArg Walk.edges <| congrArg Subtype.val <|
    hK.subsingleton_path i j |>.elim ⟨p.mapLe hHK,hp.mapLe hHK⟩ (Path.singleton hij)
  simp only [Walk.edges_map,Hom.coe_ofLE,Sym2.map_id,List.map_id_fun,id_eq] at he
  simp [he,p.adj_of_mem_edges]

 theorem exists_tree_preserving_residual {I : Type*} (Q H : SimpleGraph I)
    (R : Set I) (hconn : Q.Connected) (hHQ : H≤Q) (hforest : H.IsAcyclic)
    (hspan : ∀ i∈R,∀ j∈R,Q.Adj i j → H.Reachable i j) :
    ∃ K : SimpleGraph I,H≤K ∧ K≤Q ∧ K.IsTree ∧
      withinVertices K R=withinVertices H R := by
  obtain ⟨K,hHK,hKQ,hK⟩ := hconn.exists_isTree_le_of_le_of_isAcyclic hHQ hforest
  refine ⟨K,hHK,hKQ,hK,?_⟩
  ext i j
  constructor
  · rintro ⟨hij,hi,hj⟩
    exact ⟨acyclic_adj_of_reachable_subgraph hK.isAcyclic hHK hij
      (hspan i hi j hj (hKQ hij)),hi,hj⟩
  · rintro ⟨hij,hi,hj⟩
    exact ⟨hHK hij,hi,hj⟩

 theorem exists_tree_preserving_chosen_forest {I : Type*} (Q H : SimpleGraph I)
    (R : Set I) (hconn : Q.Connected) (hHQ : H≤Q) (hforest : H.IsAcyclic)
    (hreach : H.Reachable=(withinVertices Q R).Reachable)
    (hout : ∀ i j,H.Adj i j → i∈R) :
    ∃ K : SimpleGraph I,H≤K ∧ K≤Q ∧ K.IsTree ∧ withinVertices K R=H := by
  obtain ⟨K,hHK,hKQ,hK,he⟩ := exists_tree_preserving_residual Q H R hconn hHQ hforest
    (fun i hi j hj hij => by rw [hreach];exact (show (withinVertices Q R).Adj i j from ⟨hij,hi,hj⟩).reachable)
  refine ⟨K,hHK,hKQ,hK,he.trans ?_⟩
  ext i j
  exact ⟨fun h => h.1,fun h => ⟨h,hout i j h,hout j i h.symm⟩⟩

end MinorFreeSpanners
