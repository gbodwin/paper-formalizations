import LightSpanners.BridgeWords
import LightSpanners.BucketBudgets

namespace LightSpanners.UnitSpanningCycle
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (C : LightSpanners.UnitSpanningCycle G w)

/-- Mark the non-cycle edges at or above the last bucket scale. -/
def highChords (j : ℕ) : Set (Sym2 V) := {e | e ∉ C.cycle.edges ∧ (2:ℝ)^j ≤ w e}

theorem high_word_edges {u v : V} (p : G.Walk u v) (j : ℕ) :
    (MarkedWalk.word (C.highChords j) p).map Dart.edge =
      (C.chordEdges p).filter (fun e => (2:ℝ)^j ≤ w e) := by
  rw [MarkedWalk.word_map_edges]
  simp only [chordEdges,List.filter_filter]
  apply List.filter_congr
  intro e _
  simp [highChords,and_comm]

theorem BucketSafe.high_word {eps : ℝ} {k j : ℕ} {u v : V} {p : G.Walk u v}
    (h : C.BucketSafe eps k j p) :
    MarkedWalk.word (C.highChords j) p = C.chordDarts p := by
  unfold MarkedWalk.word chordDarts
  apply List.filter_congr
  intro d hd
  have hed : d.edge ∈ p.edges := List.mem_map.mpr ⟨d,hd,rfl⟩
  by_cases hc : d.edge ∈ C.cycle.edges
  · simp [highChords,hc]
  · have he : d.edge ∈ C.chordEdges p := by simp [chordEdges,hed,hc]
    obtain ⟨s,hs,_⟩ := h
    have hlo := (hs.2.1 d.edge he).1
    simp [highChords,hc,hlo]

theorem BucketMonotoneWalk.high_word_nil {eps : ℝ} {k j : ℕ} {extra : Bool}
    {u v : V} {p : G.Walk u v} (h : C.BucketMonotoneWalk eps k extra j p) :
    MarkedWalk.word (C.highChords j) p = [] := by
  apply (MarkedWalk.word_nil_iff _ p).mpr
  intro e he hmark
  have hch : e ∈ C.chordEdges p := by simp [chordEdges,he,hmark.1]
  exact (not_lt_of_ge hmark.2) (h.chord_weight_lt C e hch)

theorem high_word_snoc {eps : ℝ} {k j : ℕ} {extra : Bool} {u v z : V}
    {p : G.Walk u v} {q : G.Walk v z}
    (hp : C.BucketMonotoneWalk eps k extra j p)
    (hq : if extra then C.BucketExtraSafe eps k j q else C.BucketSafe eps k j q) :
    MarkedWalk.word (C.highChords j) (p.append q) = C.chordDarts q := by
  rw [MarkedWalk.word_append,hp.high_word_nil C,List.nil_append]
  exact (bucket_safe_of_mode C hq).high_word C

variable [Fintype V]

/-- Dispersion for actual bucket-monotone walks with at most k chords.
No decomposition uniqueness or global simplicity is assumed. -/
theorem BucketMonotoneWalk.unique {eps : ℝ} {k j : ℕ} {extra : Bool}
    {u v : V} {p q : G.Walk u v}
    (hp : C.BucketMonotoneWalk eps k extra j p)
    (hq : C.BucketMonotoneWalk eps k extra j q)
    (heps : 0 < eps) (hk : 0 < k)
    (hpc : (C.chordEdges p).length ≤ k) (hqc : (C.chordEdges q).length ≤ k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) : p = q := by
  induction hp with
  | nil u => cases hq; rfl
  | @snoc j u v z p r hp hr ih =>
    cases hq with
    | @snoc _ _ v' _ p' r' hp' hr' =>
      have hsafe := bucket_safe_of_mode C hr
      have hsafe' := bucket_safe_of_mode C hr'
      by_cases he : C.chordDarts r = C.chordDarts r'
      · obtain ⟨s,hs,_⟩ := hsafe
        obtain ⟨t,ht,_⟩ := hsafe'
        have hv : v = v' := hs.same_start_of_chordDarts C ht he
        subst v'
        have hrr : r = r' := (bucket_safe_of_mode C hr).eq_of_chordDarts C
          (bucket_safe_of_mode C hr') heps hk hG he
        have hppc : (C.chordEdges p).length ≤ k := by
          rw [C.chordEdges_append,List.length_append] at hpc; omega
        have hppc' : (C.chordEdges p').length ≤ k := by
          rw [C.chordEdges_append,List.length_append] at hqc; omega
        have hpp := ih hp' hppc hppc'
        rw [hpp,hrr]
      · have hpa := BucketMonotoneWalk.snoc hp hr
        have hqa := BucketMonotoneWalk.snoc hp' hr'
        have hpn : ((MarkedWalk.word (C.highChords j) (p.append r)).map Dart.edge).Nodup := by
          rw [C.high_word_edges]
          exact (hpa.chordEdges_nodup C heps hk hpc hG).filter _
        have hqn : ((MarkedWalk.word (C.highChords j) (p'.append r')).map Dart.edge).Nodup := by
          rw [C.high_word_edges]
          exact (hqa.chordEdges_nodup C heps hk hqc hG).filter _
        have hwords : MarkedWalk.word (C.highChords j) (p.append r) ≠
            MarkedWalk.word (C.highChords j) (p'.append r') := by
          rw [C.high_word_snoc hp hr,C.high_word_snoc hp' hr']; exact he
        obtain ⟨a,c,hc,hsub,e,hec,hem⟩ := MarkedWalk.exists_marked_cycle_in_union
          (C.highChords j) (p.append r) (p'.append r') hpn hqn hwords
        exact False.elim (C.no_top_bucket_cycle _ _ c hpa hqa hpc hqc heps hk hG hc hsub
          ⟨e,hec,hem.2⟩)

omit [Fintype V] in
/-- Empty blocks extend a decomposition to any larger terminal bucket index. -/
theorem BucketMonotoneWalk.pad {eps : ℝ} {k j l : ℕ} {extra : Bool}
    {u v : V} {p : G.Walk u v} (h : C.BucketMonotoneWalk eps k extra j p)
    (heps : 0 ≤ eps) (hjl : j ≤ l) : C.BucketMonotoneWalk eps k extra l p := by
  induction l, hjl using Nat.le_induction with
  | base => exact h
  | succ l _ ih =>
    have hn : if extra then C.BucketExtraSafe eps k l (.nil : G.Walk v v)
        else C.BucketSafe eps k l (.nil : G.Walk v v) := by
      cases extra with
      | false => exact C.bucketSafe_nil eps heps k l v
      | true => exact C.bucketExtraSafe_nil eps heps k l v
    simpa using BucketMonotoneWalk.snoc ih hn

/-- Lemma 5.5: endpoint uniqueness for the actual bucket-monotone safe k-paths. -/
theorem BucketMonotoneKPath.unique {eps : ℝ} {k : ℕ} {extra : Bool}
    {u v : V} {p q : G.Walk u v}
    (hp : C.BucketMonotoneKPath eps k extra p) (hq : C.BucketMonotoneKPath eps k extra q)
    (heps : 0 < eps) (hk : 0 < k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) : p = q := by
  obtain ⟨hpc,j,hp⟩ := hp
  obtain ⟨hqc,l,hq⟩ := hq
  exact (hp.pad C heps.le (Nat.le_max_left j l)).unique C
    (hq.pad C heps.le (Nat.le_max_right j l)) heps hk hpc.le hqc.le hG

end LightSpanners.UnitSpanningCycle
