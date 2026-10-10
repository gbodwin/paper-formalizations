import GreedyShortcuts.CanonicalSegments

/-! A native shortest-hop path cannot visit more than K+1 vertices of one
color if every forward same-color pair has a K-hop replacement in the fixed
relation. This uses ordinary shortest paths, not source-rebased normalized
optimality. -/
namespace GreedyShortcuts.ColoredHopBound

open Finset SimpleGraph DirectedPaths CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

 theorem fiber_card_le {G : V → V → Prop} {s t : V} {p : DWalk s t}
    (hp : Optimal G (fun _ _ => 1) p) (color : V → Option I) (c : I) (K : ℕ)
    (hshort : ∀ i j,i ≤ j → j ≤ p.length →
      color (p.getVert i) = some c → color (p.getVert j) = some c →
      ∃ q : DWalk (p.getVert i) (p.getVert j),Allowed G q ∧ q.length ≤ K) :
    (p.support.toFinset.filter (fun v => color v = some c)).card ≤ K+1 := by
  classical
  let A := (Finset.range (p.length+1)).filter (fun i => color (p.getVert i) = some c)
  have himage : p.support.toFinset.filter (fun v => color v = some c) = A.image p.getVert := by
    ext v
    simp only [Finset.mem_filter,List.mem_toFinset,Finset.mem_image]
    constructor
    · rintro ⟨hv,hc⟩
      obtain ⟨i,hi,hilen⟩ := Walk.mem_support_iff_exists_getVert.mp hv
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by simpa [hi]⟩,hi⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨p.getVert_mem_support i,(Finset.mem_filter.mp hi).2⟩
  rw [himage]
  apply Finset.card_image_le.trans
  by_cases hA : A.Nonempty
  · let a := A.min' hA
    let b := A.max' hA
    have ha : a ∈ A := Finset.min'_mem A hA
    have hb : b ∈ A := Finset.max'_mem A hA
    have hab : a ≤ b := Finset.min'_le A b hb
    have hbl : b ≤ p.length := by
      have hh := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      omega
    obtain ⟨q,hq,hqK⟩ := hshort a b hab hbl
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have hlen := (optimal_segment hp a b hab).shortest q hq
    have hlen' : (segment p a b hab).length ≤ q.length := by
      simpa only [NNReal.coe_one,unit_cost,Nat.cast_le] using hlen
    have hba : b-a ≤ K := by rw [segment_length p hab hbl] at hlen';omega
    have hsub : A ⊆ Finset.Icc a b := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le A i hi,Finset.le_max' A i hi⟩
    apply (Finset.card_le_card hsub).trans
    simpa only [Nat.card_Icc] using (show b+1-a ≤ K+1 by omega)
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [he]

/-- Count path vertices by the uncovered set and the permitted color fibers. -/
theorem length_le_of_fibers {s t : V} {p : DWalk s t} (hp : p.IsPath)
    (color : V → Option I) (A : Finset I) (U : Finset V) (K : ℕ)
    (hnode : ∀ v ∈ p.support,color v = none → v ∈ U)
    (hcolor : ∀ v ∈ p.support,∀ c,color v = some c → c ∈ A)
    (hfiber : ∀ c ∈ A,(p.support.toFinset.filter (fun v => color v = some c)).card ≤ K) :
    p.length+1 ≤ U.card+K*A.card := by
  classical
  have hsub : p.support.toFinset ⊆ U ∪ A.biUnion
      (fun c => p.support.toFinset.filter (fun v => color v = some c)) := by
    intro v hv
    have hv' := List.mem_toFinset.mp hv
    cases hc : color v with
    | none => exact Finset.mem_union_left _ (hnode v hv' hc)
    | some c => exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨c,hcolor v hv' c hc,Finset.mem_filter.mpr ⟨hv,hc⟩⟩)
  have hcard : p.support.toFinset.card = p.length+1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
  rw [← hcard]
  calc
    _ ≤ (U ∪ A.biUnion (fun c => p.support.toFinset.filter (fun v => color v = some c))).card := Finset.card_le_card hsub
    _ ≤ U.card + (A.biUnion (fun c => p.support.toFinset.filter (fun v => color v = some c))).card := Finset.card_union_le _ _
    _ ≤ U.card + ∑ c ∈ A,(p.support.toFinset.filter (fun v => color v = some c)).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ U.card + ∑ _c ∈ A,K := Nat.add_le_add_left (Finset.sum_le_sum hfiber) _
    _ = U.card+K*A.card := by simp [Nat.mul_comm]


 def admissible (color : V → Option I) (A : Finset I) (U : Finset V) (v : V) : Prop :=
  (color v = none → v ∈ U) ∧ ∀ c,color v = some c → c ∈ A

def restrict (G : V → V → Prop) (P : V → Prop) (u v : V) : Prop :=
  G u v ∧ P u ∧ P v

theorem allowed_restrict {G : V → V → Prop} {P : V → Prop} {s t : V}
    (p : DWalk s t) (hp : Allowed G p) (hP : ∀ v ∈ p.support,P v) :
    Allowed (restrict G P) p := by
  intro d hd
  exact ⟨hp d hd,hP d.fst (p.dart_fst_mem_support_of_mem_darts hd),
    hP d.snd (p.dart_snd_mem_support_of_mem_darts hd)⟩

theorem support_restrict {G : V → V → Prop} {P : V → Prop} {s t : V}
    (p : DWalk s t) (hp : Allowed (restrict G P) p) (hs : P s) :
    ∀ v ∈ p.support,P v := by
  induction p with
  | nil => simpa using hs
  | @cons s u t ha p ih =>
    have hh := (allowed_cons (restrict G P) ha p).mp hp
    intro v hv
    simp only [Walk.support_cons,List.mem_cons] at hv
    exact hv.elim (fun h => h ▸ hs) (ih hh.2 hh.1.2.2 v)

/-- Compress a supplied walk without introducing new colors or new uncovered
vertices. Every replacement is an actual walk in G. -/
theorem compress {G : V → V → Prop} (color : V → Option I)
    (A : Finset I) (U : Finset V) (K : ℕ)
    (hshort : ∀ u v c,Reachable G u v → color u = some c → color v = some c →
      ∃ q : DWalk u v,Allowed G q ∧ q.length ≤ K ∧ ∀ x ∈ q.support,color x = some c)
    {s t : V} (p : DWalk s t) (hp : Allowed G p)
    (hP : ∀ v ∈ p.support,admissible color A U v) :
    ∃ q : DWalk s t,Allowed G q ∧ q.length+1 ≤ U.card+(K+1)*A.card ∧
      ∀ v ∈ q.support,admissible color A U v := by
  classical
  let J := restrict G (admissible color A U)
  have hr : Reachable J s t := ⟨p,allowed_restrict p hp hP⟩
  let q := canonical J s t hr
  have hq := canonical_optimal J s t hr
  have hnodes := support_restrict q hq.1 (hP s p.start_mem_support)
  refine ⟨q,allowed_mono (fun _ _ h => h.1) hq.1,?_,hnodes⟩
  apply length_le_of_fibers hq.2.1 color A U (K+1)
    (fun v hv => (hnodes v hv).1) (fun v hv => (hnodes v hv).2)
  intro c hc
  apply fiber_card_le hq color c K
  intro i j hij hj hiC hjC
  have hreach : Reachable G (q.getVert i) (q.getVert j) :=
    ⟨segment q i j hij,allowed_mono (fun _ _ h => h.1)
      (allowed_subwalk hq.1 (segment_isSubwalk q i j hij))⟩
  obtain ⟨r,hgr,hrK,hrC⟩ := hshort _ _ c hreach hiC hjC
  refine ⟨r,allowed_restrict r hgr ?_,hrK⟩
  intro v hv
  have hvc := hrC v hv
  refine ⟨?_,?_⟩
  · intro hn
    simp [hvc] at hn
  · intro d hd
    have he : c = d := Option.some.inj (hvc.symm.trans hd)
    simpa [← he] using hc

end GreedyShortcuts.ColoredHopBound
