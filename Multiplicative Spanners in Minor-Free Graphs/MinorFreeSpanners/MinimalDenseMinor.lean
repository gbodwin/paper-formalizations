import MinorFreeSpanners.MinorComposition
import MinorFreeSpanners.CoreExtraction

/-! Actual finite minor-minimal dense graphs, selected by well ordering.
Nonempty target graphs are required: the empty graph must not make a
cross-multiplied density inequality vacuous. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*}
attribute [local instance] Classical.propDecidable

/-- Delete target edges without changing any host branch or internal walk. -/
def MinorModel.restrictEdges {I : Type*} {F H : SimpleGraph I} {G : SimpleGraph V}
    (M : MinorModel F G) (hH : H ≤ F) : MinorModel H G where
  branch := M.branch
  nonempty := M.nonempty
  disjoint := M.disjoint
  connected := M.connected
  adjacent := fun i j h => M.adjacent i j (hH h)

structure DenseFiniteMinor (G : SimpleGraph V) (d n : ℕ) where
  graph : SimpleGraph (Fin n)
  model : MinorModel graph G
  positive_vertices : 0 < n
  density : d*n ≤ graph.edgeFinset.card

structure MinimalDenseFiniteMinor (G : SimpleGraph V) (d n : ℕ)
    extends DenseFiniteMinor G d n where
  minimal : ∀ m (M : DenseFiniteMinor G d m),
    n+graph.edgeFinset.card ≤ m+M.graph.edgeFinset.card

/-- Every nonempty finite dense host has an actual minor minimizing
vertices plus edges among all nonempty dense finite minors. -/
theorem exists_minimal_dense_minor [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (hn : 0 < Fintype.card V)
    (hd : d*Fintype.card V ≤ G.edgeFinset.card) :
    ∃ n, Nonempty (MinimalDenseFiniteMinor G d n) := by
  classical
  let e := (Fintype.equivFin V).symm
  let F := G.comap e
  letI : DecidableRel F.Adj := fun _ _ => Classical.propDecidable _
  have hcard : F.edgeFinset.card = G.edgeFinset.card :=
    (SimpleGraph.Iso.comap e G).card_edgeFinset_eq
  let M : DenseFiniteMinor G d (Fintype.card V) := {
    graph := F
    model := MinorModel.ofEmbedding F G e.toEmbedding (fun _ _ h => h)
    positive_vertices := hn
    density := hd.trans (Nat.le_of_eq hcard.symm) }
  let P : ℕ → Prop := fun s => ∃ n, ∃ (N : DenseFiniteMinor G d n),
    n+N.graph.edgeFinset.card = s
  have hex : ∃ s, P s := ⟨_,Fintype.card V,M,rfl⟩
  obtain ⟨n,N,hN⟩ := Nat.find_spec hex
  refine ⟨n,⟨{toDenseFiniteMinor := N,minimal := ?_}⟩⟩
  intro m Q
  rw [hN]
  exact Nat.find_min' hex ⟨m,Q,rfl⟩

/-- Minimality forces the exact integer edge-density equality. The target
edge subset is constructed, and its host minor model is retained. -/
theorem MinimalDenseFiniteMinor.edge_count_eq {G : SimpleGraph V} {d n : ℕ}
    (M : MinimalDenseFiniteMinor G d n) : M.graph.edgeFinset.card = d*n := by
  classical
  have hg : GirthAbove M.graph 0 := by
    intro a p hp
    have h := hp.three_le_length
    omega
  obtain ⟨H,hH,hcard,_⟩ := exists_edge_trim M.graph (d*n) 0 M.density hg
  let Q : DenseFiniteMinor G d n := {
    graph := H
    model := M.model.restrictEdges hH
    positive_vertices := M.positive_vertices
    density := by rw [hcard] }
  have hmin := M.minimal n Q
  change n+M.graph.edgeFinset.card ≤ n+H.edgeFinset.card at hmin
  rw [hcard] at hmin
  exact Nat.le_antisymm (by omega) M.density

/-- The minimum can be compared with a dense minor on any finite vertex
 type, using an explicit graph isomorphism to a finite ordinal. -/
theorem MinimalDenseFiniteMinor.minimal_of_model {G : SimpleGraph V} {d n : ℕ}
    (M : MinimalDenseFiniteMinor G d n) {I : Type*} [Fintype I] [DecidableEq I]
    (F : SimpleGraph I) [DecidableRel F.Adj] (N : MinorModel F G) (hI : 0 < Fintype.card I)
    (hd : d*Fintype.card I ≤ F.edgeFinset.card) :
    n+M.graph.edgeFinset.card ≤ Fintype.card I+F.edgeFinset.card := by
  classical
  let e := (Fintype.equivFin I).symm
  let H := F.comap e
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hcard : H.edgeFinset.card = F.edgeFinset.card :=
    (SimpleGraph.Iso.comap e F).card_edgeFinset_eq
  let Q : DenseFiniteMinor G d (Fintype.card I) := {
    graph := H
    model := (MinorModel.ofEmbedding H F e.toEmbedding (fun _ _ h => h)).comp N
    positive_vertices := hI
    density := hd.trans (Nat.le_of_eq hcard.symm) }
  have hm := M.minimal (Fintype.card I) Q
  change n+M.graph.edgeFinset.card ≤ Fintype.card I+H.edgeFinset.card at hm
  simpa only [hcard] using hm

/-- Every actual smaller nonempty minor has density strictly below d. -/
theorem MinimalDenseFiniteMinor.smaller_minor_sparse {G : SimpleGraph V} {d n : ℕ}
    (M : MinimalDenseFiniteMinor G d n) {I : Type*} [Fintype I] [DecidableEq I]
    (F : SimpleGraph I) [DecidableRel F.Adj] (N : MinorModel F G) (hI : 0 < Fintype.card I)
    (hsmall : Fintype.card I+F.edgeFinset.card < n+M.graph.edgeFinset.card) :
    F.edgeFinset.card < d*Fintype.card I := by
  by_contra h
  exact (not_le_of_gt hsmall) (M.minimal_of_model F N hI (Nat.le_of_not_gt h))

end MinorFreeSpanners
