import GreedyShortcuts.CanonicalSavings

/-! The heavy-intersection branch for actual canonical DAG paths. -/
namespace GreedyShortcuts.HeavyCharging

open Finset SimpleGraph DirectedPaths CanonicalSegments ShortcutWalk
open SuffixIncidence SuffixIntersections CanonicalSavings
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

def starts {s t : V} (q : DWalk s t) (σ : ℕ) : Finset ℕ :=
  (Finset.range (q.length+1)).filter (fun i => i+σ/2 ≤ q.length)

def edge {s t : V} (q : DWalk s t) (σ i : ℕ) : V × V := edgeAt q (i,i+σ/2)

theorem pairedStarts_subset {s t u v : V} (q : DWalk s t) (p : DWalk u v) (σ : ℕ) :
    IntervalCharging.pairedStarts (indices q p) (σ/2) ⊆ starts q σ := by
  intro i hi
  have hh := Finset.mem_filter.mp hi
  have hhi := Finset.mem_filter.mp hh.1
  have hhj := Finset.mem_filter.mp hh.2
  exact Finset.mem_filter.mpr ⟨hhi.1,by have := Finset.mem_range.mp hhj.1; omega⟩

theorem edge_legal {G : V → V → Prop} {s t : V} {q : DWalk s t}
    (hq : Allowed G q) (hp : q.IsPath) {σ i : ℕ} (hσ : 8 ≤ σ) (hi : i ∈ starts q σ) :
    edge q σ i ∈ candidates G := by
  have hh := (Finset.mem_filter.mp hi).2
  apply (mem_candidates G _).mpr
  exact ⟨vertices_ne hp (by omega) hh,reachable_segment hq (by omega)⟩

/-- A heavy demand contributes enough genuine single-edge savings across
the short base path's fixed-separation shortcut candidates. -/
theorem row_bound {G : V → V → Prop} (hG : Acyclic G)
    {s t u v : V} {q : DWalk s t} {p : DWalk u v}
    (hq : Optimal G (fun _ _ => 1) q) (hp : Optimal G (fun _ _ => 1) p)
    (β σ : ℕ) (hσ : 8 ≤ σ) (hactive : β < p.length)
    (hheavy : σ ≤ (q.support.toFinset ∩ vertices p).card) :
    σ*(q.support.toFinset ∩ vertices p).card ≤
      8*∑ i ∈ starts q σ,demandDrop G β (edge q σ i) (u,v) := by
  let T := IntervalCharging.pairedStarts (indices q p) (σ/2)
  have hpair : (q.support.toFinset ∩ vertices p).card ≤ 2*T.card :=
    heavy_pairedStarts hG hq hp σ hσ hheavy
  have hsaving : ∀ i ∈ T, σ/2-1 ≤ demandDrop G β (edge q σ i) (u,v) := by
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hai := (Finset.mem_filter.mp hh.1).2
    have haj := (Finset.mem_filter.mp hh.2).2
    have hend : i+σ/2 ≤ q.length := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hh.2).1
      omega
    have hdrop := common_shortcut_saving hG hq hp hactive
      (show i < i+σ/2 by omega) hend
      (List.mem_toFinset.mp (vertices_subset_support p hai))
      (List.mem_toFinset.mp (vertices_subset_support p haj))
    simpa only [edge,Nat.add_sub_cancel_left] using hdrop
  have hsum : T.card*(σ/2-1) ≤ ∑ i ∈ starts q σ,demandDrop G β (edge q σ i) (u,v) := by
    calc
      T.card*(σ/2-1) = ∑ _i ∈ T, (σ/2-1) := by simp
      _ ≤ ∑ i ∈ T,demandDrop G β (edge q σ i) (u,v) := Finset.sum_le_sum hsaving
      _ ≤ _ := Finset.sum_le_sum_of_subset (pairedStarts_subset q p σ)
  have hsep := IntervalCharging.separation_saving σ hσ
  calc
    σ*(q.support.toFinset ∩ vertices p).card ≤ σ*(2*T.card) := Nat.mul_le_mul_left _ hpair
    _ ≤ 8*(T.card*(σ/2-1)) := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_left 8 hsum

noncomputable def totalDrop (G : V → V → Prop) (β : ℕ) (e : V × V) : ℕ :=
  CanonicalSuffixPath.potential G β - GraphGreedy.potential G β {e}

theorem demandDrop_sum (G : V → V → Prop) (β : ℕ) (e : V × V) :
    (∑ d ∈ candidates G,demandDrop G β e d) = totalDrop G β e := by
  unfold demandDrop totalDrop CanonicalSuffixPath.potential GraphGreedy.potential
  apply Finset.sum_tsub_distrib
  intro d hd
  exact GraphGreedy.contribution_mono β
    (hopDist_mono (fun _ _ => Or.inl) ((mem_candidates G d).mp hd).2)

theorem active_sum_le (G : V → V → Prop) (β : ℕ) (e : V × V)
    (Q : Finset (CanonicalSuffixPath.active G β)) :
    (∑ d ∈ Q,demandDrop G β e d.val) ≤ totalDrop G β e := by
  classical
  calc
    (∑ d ∈ Q,demandDrop G β e d.val) ≤ ∑ d : CanonicalSuffixPath.active G β,demandDrop G β e d.val :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ Q)
    _ = ∑ d ∈ CanonicalSuffixPath.active G β,demandDrop G β e d :=
      Finset.sum_coe_sort _ _
    _ ≤ ∑ d ∈ candidates G,demandDrop G β e d :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = totalDrop G β e := demandDrop_sum G β e

/-- The actual heavy-path family and its total intersection weight. -/
noncomputable def heavy {s t : V} (G : V → V → Prop) (β σ : ℕ) (q : DWalk s t) :
    Finset (CanonicalSuffixPath.active G β) := by
  classical
  exact Finset.univ.filter (fun d => σ ≤
    (q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).card)

noncomputable def weight {s t : V} (G : V → V → Prop) (β σ : ℕ) (q : DWalk s t) : ℕ :=
  ∑ d ∈ heavy G β σ q,(q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).card

theorem heavy_progress {G : V → V → Prop} (hG : Acyclic G)
    {s t : V} {q : DWalk s t} (hq : Optimal G (fun _ _ => 1) q)
    (β σ : ℕ) (hσ : 8 ≤ σ) (hpos : 0 < weight G β σ q) :
    ∃ e ∈ candidates G, σ*weight G β σ q ≤ 8*(q.length+1)*totalDrop G β e := by
  classical
  have hQ : (heavy G β σ q).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [weight,hz] at hpos
  obtain ⟨d,hd⟩ := hQ
  have hheavy := (Finset.mem_filter.mp hd).2
  have hcard : (q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).card ≤ q.length+1 := by
    calc
      _ ≤ q.support.toFinset.card := Finset.card_le_card Finset.inter_subset_left
      _ = q.length+1 := by rw [List.toFinset_card_of_nodup hq.2.1.support_nodup,Walk.length_support]
  have hstart : (starts q σ).Nonempty := by
    refine ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
    omega
  obtain ⟨i,hi,hbound⟩ := IntervalCharging.exists_scaled_column (heavy G β σ q) (starts q σ)
    hstart (fun d => (q.support.toFinset ∩ vertices (CanonicalSuffixPath.path G β d)).card)
    (fun i d => demandDrop G β (edge q σ i) d.val) (fun i => totalDrop G β (edge q σ i)) σ 8
    (by
      intro d hd
      apply row_bound hG hq (CanonicalSuffixPath.path_optimal G β d) β σ hσ
      · rw [CanonicalSuffixPath.path_length]
        exact (Finset.mem_filter.mp d.property).2
      · exact (Finset.mem_filter.mp hd).2)
    (fun i _ => active_sum_le G β (edge q σ i) (heavy G β σ q))
  refine ⟨edge q σ i,edge_legal hq.1 hq.2.1 hσ hi,hbound.trans ?_⟩
  have hc : (starts q σ).card ≤ q.length+1 := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hc)

/-- Heavy branch of the high-score path dichotomy, with an explicit constant. -/
theorem heavy_relative {G : V → V → Prop} (hG : Acyclic G)
    {s t : V} {q : DWalk s t} (hq : Optimal G (fun _ _ => 1) q)
    (β σ : ℕ) (hβ : 8 ≤ β) (hσ : 8 ≤ σ)
    (hshort : q.length+1 ≤ β/8) (hpos : 0 < CanonicalSuffixPath.potential G β)
    (hweight : β*CanonicalSuffixPath.potential G β ≤ 512*Fintype.card V*weight G β σ q) :
    ∃ e ∈ candidates G, σ*CanonicalSuffixPath.potential G β ≤
      512*Fintype.card V*totalDrop G β e := by
  have hw : 0 < weight G β σ q := by nlinarith
  obtain ⟨e,he,hh⟩ := heavy_progress hG hq β σ hσ hw
  refine ⟨e,he,?_⟩
  have hlen : 8*(q.length+1) ≤ β := by omega
  have hh' := hh.trans (Nat.mul_le_mul_right (totalDrop G β e) hlen)
  have hh'' := Nat.mul_le_mul_left (512*Fintype.card V) hh'
  have hw' := Nat.mul_le_mul_left σ hweight
  have hfinal : β*(σ*CanonicalSuffixPath.potential G β) ≤
      β*(512*Fintype.card V*totalDrop G β e) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hfinal (by omega)

end GreedyShortcuts.HeavyCharging
