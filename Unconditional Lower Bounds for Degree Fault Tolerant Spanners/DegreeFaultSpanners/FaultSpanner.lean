import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.ENat.Monoid

/-!
# Degree-fault spanners and edge forcing

The unweighted specialization of Definition 3 of Bodwin--Lopez,
*Unconditional Lower Bounds for Degree Fault Tolerant Spanners*,
arXiv:2607.07576v1. Faults are actual spanning subgraphs of the input graph;
the number of incident faulty edges is bounded at every vertex.

`IsDegreeFaultSpanner` uses replacement walks, and
`isDegreeFaultSpanner_iff_edist` proves that, for positive integral stretch,
this is precisely the paper's extended-shortest-distance condition, including
disconnected graphs. `EdgeForcingCertificate` isolates the last step of the
paper's lower-bound argument without assuming its geometric construction.

The stretch-one case is proved separately for arbitrary graphs, and the
complete graph supplies an exact `n.choose 2` lower bound. This avoids using
the paper's point-line edge count at `k = 1`, when its direction parametrization
has duplicates.
-/

namespace DegreeFaultSpanners

open SimpleGraph

variable {V : Type*}

/-- Every input walk has a replacement whose number of edges grows by at most `t`. -/
def WalkStretch (G H : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ u v (p : G.Walk u v), ∃ q : H.Walk u v, q.length ≤ t * p.length

/-- Extended-distance stretch, with infinite distance for disconnected vertices. -/
def DistanceStretch (G H : SimpleGraph V) (t : ℕ) : Prop :=
  ∀ u v, H.edist u v ≤ (t : ℕ∞) * G.edist u v

/-- A finite upper bound on extended distance is witnessed by an actual walk. -/
theorem exists_walk_length_le_iff {G : SimpleGraph V} {u v : V} {t : ℕ} :
    (∃ p : G.Walk u v, p.length ≤ t) ↔ G.edist u v ≤ (t : ℕ∞) := by
  constructor
  · rintro ⟨p, hp⟩
    exact p.edist_le.trans (ENat.natCast_le_natCast.mpr hp)
  · intro hd
    have hfin : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfin
    refine ⟨p, ENat.natCast_le_natCast.mp ?_⟩
    rwa [hp]

/-- The absence of short walks is exactly a strict extended-distance lower bound. -/
theorem no_short_walk_iff_edist_gt {G : SimpleGraph V} {u v : V} {t : ℕ} :
    (∀ p : G.Walk u v, t < p.length) ↔ (t : ℕ∞) < G.edist u v := by
  constructor
  · intro h
    apply lt_of_not_ge
    intro hd
    obtain ⟨p, hp⟩ := exists_walk_length_le_iff.mpr hd
    exact (Nat.not_lt_of_ge hp) (h p)
  · intro h p
    apply Nat.lt_of_not_ge
    intro hp
    exact (not_le_of_gt h) (exists_walk_length_le_iff.mp ⟨p, hp⟩)

/-- Replacing each edge suffices to replace every walk. -/
theorem walkStretch_iff_edges {G H : SimpleGraph V} {t : ℕ} :
    WalkStretch G H t ↔
      ∀ u v, G.Adj u v → ∃ q : H.Walk u v, q.length ≤ t := by
  constructor
  · intro h u v huv
    obtain ⟨q, hq⟩ := h u v huv.toWalk
    exact ⟨q, by simpa only [SimpleGraph.Adj.length_toWalk, Nat.mul_one] using hq⟩
  · intro h u v p
    induction p with
    | nil => exact ⟨.nil, by simp⟩
    | @cons u v w huv p ih =>
      obtain ⟨q, hq⟩ := h u v huv
      obtain ⟨r, hr⟩ := ih
      refine ⟨q.append r, ?_⟩
      simpa [Nat.mul_add, Nat.add_comm] using Nat.add_le_add hq hr

/-- The walk formulation is the extended-distance formulation for positive stretch.
The positivity condition handles the convention `0 * ⊤ = 0`. -/
theorem walkStretch_iff_distanceStretch {G H : SimpleGraph V} {t : ℕ}
    (ht : 0 < t) : WalkStretch G H t ↔ DistanceStretch G H t := by
  constructor
  · intro h u v
    by_cases htop : G.edist u v = ⊤
    · simp [htop, Nat.ne_of_gt ht]
    · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
      obtain ⟨q, hq⟩ := h u v p
      calc
        H.edist u v ≤ (q.length : ℕ∞) := q.edist_le
        _ ≤ ((t * p.length : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr hq
        _ = (t : ℕ∞) * G.edist u v := by rw [ENat.natCast_mul, hp]
  · intro h u v p
    have hd : H.edist u v ≤ ((t * p.length : ℕ) : ℕ∞) := by
      calc
        H.edist u v ≤ (t : ℕ∞) * G.edist u v := h u v
        _ ≤ (t : ℕ∞) * (p.length : ℕ∞) := by
          apply (ENat.mul_le_mul_left_iff (by simp [Nat.ne_of_gt ht])
            (ENat.natCast_ne_top t)).mpr
          exact p.edist_le
        _ = ((t * p.length : ℕ) : ℕ∞) := (ENat.natCast_mul _ _).symm
    have hfin : H.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd
    obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfin
    refine ⟨q, ENat.natCast_le_natCast.mp ?_⟩
    rwa [hq]

section Finite

/-- A fault graph has at most `f` incident edges at every vertex.
Using `ncard` avoids requiring a decidable adjacency relation in the API. -/
def HasDegreeBound [Fintype V] (F : SimpleGraph V) (f : ℕ) : Prop :=
  ∀ v, (F.neighborSet v).ncard ≤ f

variable [Fintype V]

/-- The allowed failures are a subgraph of the input, with pointwise degree bound. -/
def AdmissibleFault (G : SimpleGraph V) (f : ℕ) (F : SimpleGraph V) : Prop :=
  F ≤ G ∧ HasDegreeBound F f

/-- Definition 3 for finite, simple, unweighted graphs and integral stretch. -/
def IsDegreeFaultSpanner (G H : SimpleGraph V) (f t : ℕ) : Prop :=
  H ≤ G ∧ ∀ F, AdmissibleFault G f F → WalkStretch (G \ F) (H \ F) t

/-- The bound in `HasDegreeBound` is exactly mathlib's graph degree bound. -/
theorem hasDegreeBound_iff_degree (F : SimpleGraph V) (f : ℕ)
    [DecidableRel F.Adj] :
    HasDegreeBound F f ↔ ∀ v, F.degree v ≤ f := by
  simp [HasDegreeBound]

@[simp] theorem hasDegreeBound_bot (f : ℕ) :
    HasDegreeBound (⊥ : SimpleGraph V) f := by
  intro v
  simp

@[simp] theorem admissibleFault_bot (G : SimpleGraph V) (f : ℕ) :
    AdmissibleFault G f ⊥ :=
  ⟨bot_le, hasDegreeBound_bot f⟩

theorem HasDegreeBound.mono {F : SimpleGraph V} {f g : ℕ}
    (h : HasDegreeBound F f) (hfg : f ≤ g) : HasDegreeBound F g :=
  fun v ↦ (h v).trans hfg

/-- Deleting some faulty edges cannot increase the degree budget. -/
theorem HasDegreeBound.of_le {F F' : SimpleGraph V} {f : ℕ}
    (h : HasDegreeBound F f) (hle : F' ≤ F) : HasDegreeBound F' f := by
  intro v
  exact (Set.ncard_le_ncard (SimpleGraph.neighborSet_mono hle v)).trans (h v)

/-- Smaller fault budgets impose weaker spanner requirements. -/
theorem IsDegreeFaultSpanner.mono_faults {G H : SimpleGraph V} {f g t : ℕ}
    (h : IsDegreeFaultSpanner G H g t) (hfg : f ≤ g) :
    IsDegreeFaultSpanner G H f t := by
  refine ⟨h.1, fun F hF ↦ h.2 F ⟨hF.1, hF.2.mono hfg⟩⟩

/-- Larger stretch imposes a weaker spanner requirement. -/
theorem IsDegreeFaultSpanner.mono_stretch {G H : SimpleGraph V} {f s t : ℕ}
    (h : IsDegreeFaultSpanner G H f s) (hst : s ≤ t) :
    IsDegreeFaultSpanner G H f t := by
  refine ⟨h.1, ?_⟩
  intro F hF u v p
  obtain ⟨q, hq⟩ := h.2 F hF u v p
  exact ⟨q, hq.trans (Nat.mul_le_mul_right _ hst)⟩

/-- Keeping every edge is always a valid spanner when `t ≥ 1`. -/
theorem isDegreeFaultSpanner_self (G : SimpleGraph V) (f : ℕ) {t : ℕ}
    (ht : 1 ≤ t) : IsDegreeFaultSpanner G G f t := by
  refine ⟨le_rfl, ?_⟩
  intro F hF u v p
  refine ⟨p, ?_⟩
  simpa using Nat.mul_le_mul_right p.length ht

/-- Exact bridge to the paper's definition, including disconnected pairs. -/
theorem isDegreeFaultSpanner_iff_edist {G H : SimpleGraph V} {f t : ℕ}
    (ht : 0 < t) :
    IsDegreeFaultSpanner G H f t ↔
      H ≤ G ∧ ∀ F, AdmissibleFault G f F →
        ∀ u v, (H \ F).edist u v ≤ (t : ℕ∞) * (G \ F).edist u v := by
  simp only [IsDegreeFaultSpanner, walkStretch_iff_distanceStretch ht, DistanceStretch]

/-- The surviving endpoints of an edge must remain joined by a walk of length at most `t`. -/
theorem IsDegreeFaultSpanner.edge_replacement {G H F : SimpleGraph V}
    {f t : ℕ} (h : IsDegreeFaultSpanner G H f t)
    (hF : AdmissibleFault G f F) {u v : V}
    (huv : G.Adj u v) (hnot : ¬ F.Adj u v) :
    ∃ q : (H \ F).Walk u v, q.length ≤ t := by
  exact (walkStretch_iff_edges.mp (h.2 F hF)) u v ⟨huv, hnot⟩

/-- An admissible fault set avoids the target edge but destroys every short
alternative walk. The deleted target edge is an unordered pair. -/
def EdgeForcingCertificate (G : SimpleGraph V) (f t : ℕ) (u v : V) : Prop :=
  G.Adj u v ∧ ∃ F : SimpleGraph V,
    AdmissibleFault G f F ∧ ¬ F.Adj u v ∧
      ∀ p : ((G \ F).deleteEdges {s(u, v)}).Walk u v, t < p.length

/-- Equivalent certificate stated entirely in terms of extended shortest distances. -/
theorem edgeForcingCertificate_iff_edist {G : SimpleGraph V} {f t : ℕ} {u v : V} :
    EdgeForcingCertificate G f t u v ↔
      G.Adj u v ∧ ∃ F : SimpleGraph V,
        AdmissibleFault G f F ∧ ¬ F.Adj u v ∧
          (t : ℕ∞) < ((G \ F).deleteEdges {s(u, v)}).edist u v := by
  simp only [EdgeForcingCertificate, no_short_walk_iff_edist_gt]

/-- A matching containing the protected edge gives a forcing certificate when
removing that matching destroys every short walk between the protected endpoints.
The actual fault graph omits the protected edge from the matching. -/
theorem forcing_certificate_of_matching_obstruction
    {G Q : SimpleGraph V} {u v : V} {t : ℕ}
    (huv : G.Adj u v) (hQG : Q ≤ G) (hQuv : Q.Adj u v)
    (hdeg : HasDegreeBound Q 1)
    (hlong : ∀ p : (G \ Q).Walk u v, t < p.length) :
    EdgeForcingCertificate G 1 t u v := by
  let F := Q.deleteEdges {s(u, v)}
  have hFQ : F ≤ Q := Q.deleteEdges_le _
  have hsurvives : (G \ F).Adj u v := ⟨hQG hQuv, by simp [F]⟩
  refine ⟨huv, F, ⟨hFQ.trans hQG, hdeg.of_le hFQ⟩, hsurvives.2, ?_⟩
  intro p
  have hle : (G \ F).deleteEdges {s(u, v)} ≤ G \ Q := by
    intro a b hab
    obtain ⟨hGF, hne⟩ := SimpleGraph.deleteEdges_adj.mp hab
    refine ⟨hGF.1, ?_⟩
    intro hQab
    exact hGF.2 (SimpleGraph.deleteEdges_adj.mpr ⟨hQab, hne⟩)
  simpa using hlong (p.mapLe hle)

/-- A version of the forcing argument convenient for proofs that directly show
every short surviving walk traverses the target edge. -/
theorem edge_mem_of_short_walks {G H F : SimpleGraph V} {f t : ℕ} {u v : V}
    (h : IsDegreeFaultSpanner G H f t) (hF : AdmissibleFault G f F)
    (huv : G.Adj u v) (hnot : ¬ F.Adj u v)
    (hshort : ∀ p : (G \ F).Walk u v, p.length ≤ t → s(u, v) ∈ p.edges) :
    H.Adj u v := by
  obtain ⟨q, hq⟩ := h.edge_replacement hF huv hnot
  have hle : H \ F ≤ G \ F := sdiff_le_sdiff_right h.1
  have he := hshort (q.mapLe hle) (by simpa using hq)
  have hqadj : (H \ F).Adj u v := q.adj_of_mem_edges (by simpa using he)
  exact hqadj.1

/-- Edge-forcing lemma: a degree-fault spanner must contain every certified edge. -/
theorem edge_mem_of_forcing_certificate {G H : SimpleGraph V} {f t : ℕ} {u v : V}
    (h : IsDegreeFaultSpanner G H f t)
    (hc : EdgeForcingCertificate G f t u v) : H.Adj u v := by
  rcases hc with ⟨huv, F, hF, hnot, hlong⟩
  by_contra hmissing
  obtain ⟨q, hq⟩ := h.edge_replacement hF huv hnot
  have hdelete : (H \ F).deleteEdges {s(u, v)} = H \ F := by
    apply SimpleGraph.deleteEdges_eq_self.mpr
    apply Set.disjoint_singleton_right.mpr
    intro he
    exact hmissing ((SimpleGraph.mem_edgeSet _).mp he).1
  have hle : H \ F ≤ (G \ F).deleteEdges {s(u, v)} := by
    rw [← hdelete]
    exact SimpleGraph.deleteEdges_mono (sdiff_le_sdiff_right h.1)
  have hgt := hlong (q.mapLe hle)
  exact (Nat.not_lt_of_ge hq) (by simpa using hgt)

/-- If every input edge has a forcing certificate, no proper spanner exists. -/
theorem eq_of_all_edges_forced {G H : SimpleGraph V} {f t : ℕ}
    (h : IsDegreeFaultSpanner G H f t)
    (hforced : ∀ u v, G.Adj u v → EdgeForcingCertificate G f t u v) :
    H = G := by
  apply le_antisymm h.1
  intro u v huv
  exact edge_mem_of_forcing_certificate h (hforced u v huv)

/-- For stretch one, even the empty fault set forces every original edge. -/
theorem one_spanner_eq {G H : SimpleGraph V} {f : ℕ}
    (h : IsDegreeFaultSpanner G H f 1) : H = G := by
  apply le_antisymm h.1
  intro u v huv
  obtain ⟨q, hq⟩ := h.edge_replacement (admissibleFault_bot G f) huv (by simp)
  have hn : q.length ≠ 0 := fun hz ↦ huv.ne (q.eq_of_length_eq_zero hz)
  have hlen : q.length = 1 := le_antisymm hq (Nat.one_le_iff_ne_zero.mpr hn)
  exact (q.adj_of_length_eq_one hlen).1

@[simp] theorem isDegreeFaultSpanner_one_iff {G H : SimpleGraph V} {f : ℕ} :
    IsDegreeFaultSpanner G H f 1 ↔ H = G := by
  refine ⟨one_spanner_eq, ?_⟩
  intro h
  subst H
  exact isDegreeFaultSpanner_self G f le_rfl

/-- Exact edge count of every stretch-one degree-fault spanner of a complete graph. -/
theorem complete_one_spanner_edge_count {H : SimpleGraph V} {f : ℕ}
    (h : IsDegreeFaultSpanner ⊤ H f 1) :
    H.edgeSet.ncard = (Fintype.card V).choose 2 := by
  classical
  rw [one_spanner_eq h, ← Set.fintypeCard_eq_ncard,
    SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]

/-- The `k = 1` lower-bound witness works for every vertex count and fault budget. -/
theorem exists_complete_one_lower_bound (n f : ℕ) :
    ∃ G : SimpleGraph (Fin n),
      G.edgeSet.ncard = n.choose 2 ∧
      ∀ H, IsDegreeFaultSpanner G H f 1 → H.edgeSet.ncard = n.choose 2 := by
  refine ⟨⊤, ?_, ?_⟩
  · simpa using complete_one_spanner_edge_count (isDegreeFaultSpanner_self
      (⊤ : SimpleGraph (Fin n)) f (t := 1) le_rfl)
  · intro H h
    simpa using complete_one_spanner_edge_count h

end Finite

end DegreeFaultSpanners
