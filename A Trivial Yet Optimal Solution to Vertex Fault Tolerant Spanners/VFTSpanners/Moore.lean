import VFTSpanners.Extremal
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace VFTSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Two short simple paths with the same endpoints coincide in a graph
with no cycle of length at most `2*r`. -/
theorem HighGirth.short_paths_unique {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (hg : HighGirth G (2*r)) {u v : V} {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length ≤ 2*r) :
    p = q := by
  by_contra hne
  obtain ⟨a, _, _, c, hc, hcl⟩ := hp.exists_isCycle_length_le_add_of_ne hq hne
  exact (not_le_of_gt (hg a c hc)) (hcl.trans hlen)

/-- A neighbor of a short path's endpoint can lie on the path only if it
is the preceding vertex. This is the no-collision step of the Moore count. -/
theorem HighGirth.neighbor_not_mem_path {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ} (hg : HighGirth G (2*r))
    {u v z : V} {p : G.Walk u v} (hp : p.IsPath)
    (hlen : p.length + 1 ≤ 2*r) (hadj : G.Adj v z)
    (hz : z ≠ p.penultimate) : z ∉ p.support := by
  intro hmem
  let q := p.dropUntil z hmem
  have heq : q = hadj.symm.toWalk := hg.short_paths_unique (hp.dropUntil hmem)
    hadj.symm.isPath_toWalk (by
      have hq := p.length_dropUntil_le_length hmem
      simpa [q] using (by omega : (p.dropUntil z hmem).length + 1 ≤ 2*r))
  have he : s(v,z) ∈ p.edges := by
    have he' : s(v,z) ∈ q.edges := by simp [heq, Sym2.eq_swap]
    exact (p.isSubwalk_dropUntil hmem).edges_subset he'
  exact hz (hp.eq_penultimate_of_mem_edges he)

/-- The finite type of rooted simple paths of exactly `t` edges. -/
abbrev RootedPaths {V : Type*} (G : SimpleGraph V) (root : V) (t : ℕ) :=
  Σ v : V, {p : G.Walk root v // p.IsPath ∧ p.length = t}

/-- At least `d` extensions per path, after excluding its preceding vertex. -/
theorem rootedPaths_growth {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (r t d : ℕ)
    (hg : HighGirth G (2*r)) (ht : t < r)
    (hdeg : ∀ v, d+1 ≤ G.degree v) :
    d * Fintype.card (RootedPaths G root t) ≤
      Fintype.card (RootedPaths G root (t+1)) := by
  classical
  let choices (p : RootedPaths G root t) : Finset V :=
    (G.neighborFinset p.1).erase p.2.1.penultimate
  let extend : (Σ p : RootedPaths G root t, {z // z ∈ choices p}) →
      RootedPaths G root (t+1) := fun ⟨p,z⟩ =>
    ⟨z.1, p.2.1.concat (G.mem_neighborFinset _ _ |>.mp
      (Finset.mem_erase.mp z.2).2),
      p.2.2.1.concat (hg.neighbor_not_mem_path p.2.2.1 (by rw [p.2.2.2]; omega)
        (G.mem_neighborFinset _ _ |>.mp (Finset.mem_erase.mp z.2).2)
        (Finset.mem_erase.mp z.2).1) _,
      by simp [p.2.2.2]⟩
  have hinj : Function.Injective extend := by
    rintro ⟨⟨v,p,hp⟩,z,hz⟩ ⟨⟨v',p',hp'⟩,z',hz'⟩ he
    have hzz : z = z' := congrArg Sigma.fst he
    subst z'
    have haz : G.Adj v z := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz).2
    have haz' : G.Adj v' z := (G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hz').2
    have hwalk : p.concat haz = p'.concat haz' := by
      exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
    obtain ⟨hvv,hpp⟩ := Walk.concat_inj hwalk
    subst v'
    have hpp' : p = p' := by simpa using hpp
    subst p'
    rfl
  have hcount := Fintype.card_le_of_injective extend hinj
  calc
    d * Fintype.card (RootedPaths G root t) =
        ∑ _p : RootedPaths G root t, d := by simp [Nat.mul_comm]
    _ ≤ ∑ p : RootedPaths G root t, (choices p).card := by
      apply Finset.sum_le_sum
      intro p _
      have hb := Finset.pred_card_le_card_erase (s := G.neighborFinset p.1)
        (a := p.2.1.penultimate)
      have hd := hdeg p.1
      change d ≤ ((G.neighborFinset p.1).erase p.2.1.penultimate).card
      change d+1 ≤ (G.neighborFinset p.1).card at hd
      omega
    _ = Fintype.card (Σ p : RootedPaths G root t, {z // z ∈ choices p}) := by
      simp [Fintype.card_sigma]
    _ ≤ _ := hcount

/-- The elementary minimum-degree Moore bound, in integer-power form. -/
theorem moore_min_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (r d : ℕ)
    (hg : HighGirth G (2*r)) (hdeg : ∀ v, d+1 ≤ G.degree v) :
    d^r ≤ Fintype.card V := by
  classical
  have lower : ∀ t ≤ r, d^t ≤ Fintype.card (RootedPaths G root t) := by
    intro t ht
    induction t with
    | zero =>
      have h : Nonempty (RootedPaths G root 0) := ⟨⟨root,.nil,by simp⟩⟩
      exact Fintype.card_pos_iff.mpr h
    | succ t ih =>
      have h := rootedPaths_growth G root r t d hg (by omega) hdeg
      calc
        d^(t+1) = d*d^t := by rw [pow_succ, Nat.mul_comm]
        _ ≤ d * Fintype.card (RootedPaths G root t) :=
          Nat.mul_le_mul_left d (ih (by omega))
        _ ≤ _ := h
  apply (lower r le_rfl).trans
  apply Fintype.card_le_of_injective (fun p : RootedPaths G root r => p.1)
  rintro ⟨v,p,hp⟩ ⟨w,q,hq⟩ hvw
  dsimp at hvw
  subst w
  have heq := hg.short_paths_unique hp.1 hq.1 (by omega)
  subst q
  rfl

/-- Exact edge loss on removing a vertex from a finset-induced graph. -/
theorem induced_erase_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (v : {x // x ∈ U}) :
    (G.induce (↑(U.erase v.1) : Set V)).edgeFinset.card =
      (G.induce (↑U : Set V)).edgeFinset.card -
        (G.induce (↑U : Set V)).degree v := by
  classical
  let e : ({v}ᶜ : Set {x // x ∈ U}) ≃ {x // x ∈ U.erase v.1} :=
    (Equiv.subtypeSubtypeEquivSubtypeExists (fun x => x ∈ U) (fun x => x ≠ v)).trans
      (Equiv.subtypeEquivRight (by
        intro x
        simp only [Finset.mem_erase, Subtype.ext_iff, ne_eq]
        aesop))
  let i : ((G.induce (↑U : Set V)).induce ({v}ᶜ : Set {x // x ∈ U})) ≃g
      G.induce (↑(U.erase v.1) : Set V) := RelIso.mk e (by intro x y; rfl)
  rw [← i.card_edgeFinset_eq, card_edgeFinset_induce_compl_singleton,
    card_edgeFinset_deleteIncidenceSet]

/-- Pruning in a strict integer-density form. A graph with more than `d*n`
edges contains a nonempty induced subgraph of minimum degree at least `d+1`.
Choose a smallest vertex set still exceeding that density. -/
theorem exists_dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (hdense : d * Fintype.card V < G.edgeFinset.card) :
    ∃ U : Finset V, U.Nonempty ∧
      ∀ v : {x // x ∈ U}, d+1 ≤ (G.induce (↑U : Set V)).degree v := by
  classical
  let candidates := (Finset.univ : Finset (Finset V)).filter
    (fun U : Finset V => d*U.card < (G.induce (↑U : Set V)).edgeFinset.card)
  have hfull : (Finset.univ : Finset V) ∈ candidates := by
    have he : (G.induce (↑(Finset.univ : Finset V) : Set V)).edgeFinset.card =
        G.edgeFinset.card := by
      let e : (↑(Finset.univ : Finset V) : Set V) ≃ V :=
        { toFun := Subtype.val
          invFun := fun v => ⟨v, Finset.mem_univ v⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let i : G.induce (↑(Finset.univ : Finset V) : Set V) ≃g G :=
        RelIso.mk e (by intro x y; rfl)
      exact i.card_edgeFinset_eq
    simpa [candidates, he] using hdense
  obtain ⟨U,hU,hmin⟩ := Finset.exists_min_image candidates Finset.card ⟨_,hfull⟩
  have hd : d*U.card < (G.induce (↑U : Set V)).edgeFinset.card :=
    (Finset.mem_filter.mp hU).2
  have hUne : U.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    subst U
    have hb := (G.induce (↑(∅ : Finset V) : Set V)).card_edgeFinset_le_card_choose_two
    simp at hb hd
    exact hd hb
  refine ⟨U,hUne,?_⟩
  intro v
  by_contra hlow
  have hdeg : (G.induce (↑U : Set V)).degree v ≤ d := by omega
  have hbound := (G.induce (↑U : Set V)).degree_le_card_edgeFinset v
  have he := induced_erase_edge_count G U v
  have hc := Finset.card_erase_of_mem v.2
  have hpos : 1 ≤ U.card := Finset.one_le_card.mpr hUne
  have hmul : d*(U.erase v.1).card + d = d*U.card := by
    rw [hc]
    have heq := congrArg (fun x => d*x) (Nat.sub_add_cancel hpos)
    simpa only [Nat.mul_add, Nat.mul_one] using heq
  have hdel : U.erase v.1 ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hsum := Nat.sub_add_cancel hbound
    nlinarith
  have hsmall := hmin (U.erase v.1) hdel
  omega

/-- Inducing a graph preserves a lower bound on girth. -/
theorem HighGirth.induce {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hg : HighGirth G k) (U : Set V) : HighGirth (G.induce U) k := by
  intro v p hp
  let i : G.induce U →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  have h := hg v.1 (p.map i) (hp.map Subtype.val_injective)
  exact (p.length_map i) ▸ h

/-- A uniform coarse Moore bound for arbitrary finite simple graphs.
The constant `2` is independent of both the vertex count and `r`. -/
theorem moore_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r) (hg : HighGirth G (2*r)) :
    G.edgeFinset.card^r ≤ 2^r * (Fintype.card V)^(r+1) := by
  classical
  let n := Fintype.card V
  let m := G.edgeFinset.card
  change m^r ≤ 2^r * n^(r+1)
  by_cases hn : n = 0
  · have hb := G.card_edgeFinset_le_card_choose_two
    change m ≤ n.choose 2 at hb
    simp [hn] at hb
    simp [hb, hn, show r ≠ 0 by omega]
  have hnpos : 0 < n := by omega
  by_cases hm : m ≤ n
  · calc
      m^r ≤ n^r := Nat.pow_le_pow_left hm r
      _ ≤ n^(r+1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 2^r*n^(r+1) := Nat.le_mul_of_pos_left _ (by positivity)
  let d := (m-1)/n
  have hd : d*n < m := by
    have h := Nat.div_mul_le_self (m-1) n
    dsimp [d]
    omega
  obtain ⟨U,hU,hdeg⟩ := exists_dense_core G d hd
  have hpow : d^r ≤ n := by
    have h := moore_min_degree (G.induce (↑U : Set V))
      ⟨hU.choose,hU.choose_spec⟩ r d (hg.induce _) hdeg
    have hcard : U.card ≤ n := Finset.card_le_univ U
    have hcardU : Fintype.card (↑U : Set V) = U.card := by
      calc
        _ = (↑U : Set V).ncard := Set.fintypeCard_eq_ncard _
        _ = U.card := Set.ncard_coe_finset U
    have h' : d^r ≤ U.card := hcardU ▸ h
    exact h'.trans hcard
  have hdpos : 1 ≤ d := by
    apply Nat.le_div_iff_mul_le hnpos |>.mpr
    omega
  have hmupper : m ≤ (d+1)*n := by
    have h := Nat.lt_mul_div_succ (m-1) hnpos
    have hsub : m-1+1 = m := Nat.sub_add_cancel (by omega)
    dsimp [d]
    nlinarith only [h, hsub]
  have hm2 : m ≤ 2*d*n := by
    nlinarith
  calc
    m^r ≤ (2*d*n)^r := Nat.pow_le_pow_left hm2 r
    _ = 2^r*d^r*n^r := by simp only [mul_pow]
    _ ≤ 2^r*n*n^r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow)
    _ = 2^r*n^(r+1) := by rw [pow_succ]; ring

/-- The Moore bound for the paper's exact finite extremal function. -/
theorem extremalEdges_moore (n r : ℕ) (hr : 1 ≤ r) :
    (extremalEdges n (2*r))^r ≤ 2^r*n^(r+1) := by
  classical
  let S := (Finset.univ : Finset (SimpleGraph (Fin n))).filter
    (fun G => HighGirth G (2*r))
  have hS : S.Nonempty := by
    refine ⟨⊥,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    intro v p hp
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h p => exact h.elim
  obtain ⟨G,hG,hmax⟩ := Finset.exists_max_image S
    (fun G => G.edgeFinset.card) hS
  have hex : extremalEdges n (2*r) ≤ G.edgeFinset.card := by
    apply Finset.sup_le
    intro K hK
    exact hmax K hK
  apply (Nat.pow_le_pow_left hex r).trans
  simpa using moore_edge_bound G r hr (Finset.mem_filter.mp hG).2

end VFTSpanners
